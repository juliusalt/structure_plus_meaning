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
  \<open>ML \<open>check \<^theory> "P" ["d\<^sub>1", \<dots>, "d\<^sub>n"]\<close>\<close>, the structure's @{text check} (the harness
  places it; the repository's theory headers declare no keywords, so the frame adds none), refuses
  the theory, naming the entry, unless for every named entry \<open>d\<close>:

  \<^item> (a), (b) a contract stands in a required form. A binary entry: an interpretation of
    @{text presented_relation_contract} (an interpretation of @{text presented_function_contract}
    registers its graph relation so) whose observation is \<open>\<lambda>p q. (d, Pair_Term p q) \<in> positive_meaning P\<close>;
    its two classes are presentation classes by the locale, so the contract's invariance over every
    presentation is the locale's theorem. A unary entry: a theorem of this theory
    \<open>(d, p) \<in> positive_meaning P \<longleftrightarrow> presented_predicate R Q p\<close> over a presentation class
    \<open>presentation_class R D A\<close> (a registration or a theorem of this theory), invariant over
    presentations by @{text presentation_class.predicate_invariance};
  \<^item> (c) no statement of that contract (its classes, relation or predicate and observation) reaches,
    through the shared constant closure (@{text Isabelle_Constant_Closure}: kernel definitions,
    followed to every constant they mention) and through the definitions of every type it reaches
    (datatype constructors, type definitions' representations), a bootstrap-loop presentation
    relation or datatype as task 381's entry lists them (@{text bootstrap_constants},
    @{text bootstrap_types}); a native program defined beside them is native content and passes;
  \<^item> (f) every store search that closure reaches is a carrier index's own. A store search is an
    application of a store operation (a constant of the binary and path stores or the red-black tree,
    a store's constructors excepted) that the contract's statements, or the definitions they reach
    outside the stores, hold. A carrier index instance (@{text native_carrier_index}) is a
    registration, an instance theorem, or @{text native_store_search_program.index} at an
    interpretation of the path store's search program. An application at closed arguments (a native
    search at its sites) is an index's own when the index's site and checker (a search program's
    program and sites) reach it with every argument standing in them; an application at open
    arguments, when the index's build, search or key presentation reaches its operation. An
    application the given's package program reaches is the given's: reported, not required. Every
    store an answer adds needs an index of its own; the carrier an index is stated for is not read;
  \<^item> (d) a theorem of this theory states the notion's clause @{text renaming_equivariant} of the
    contract's relation (over the product of its classes' domains) or predicate (over its class's
    domain) at the use action the classes derive from their constructions: the product, list,
    finite-set, library finite-set and composed classes derive it from their components; a subdomain
    class (@{text presentation_class_subdomain}) from its source class, restricted when this theory
    states the restriction as @{text renaming_action} (@{text renaming_action_subdomain}); a class of
    a notion from its presenter: the environment, site-context, program-entry, site and use actions of
    @{text Factor_Use_Renaming} for classes presented by @{const environment_value_presents},
    @{const site_value_presents}, @{const program_entry_value_presents}, @{const site_data_term} and
    @{const use_data_term}; the trivial action (@{thm [source] permutation_renaming_action}) for a
    class over a type built only from constructors of exact values (@{text use_free_constructors}),
    and for an optional address (@{const optional_payload_term}), a \<open>local_address option\<close> read as a
    payload. Any other class is refused, named. The frame states the clause; an action the answer
    supplies never enters it.

  These are proxies read on Isabelle text, the bootstrap verifier's, until native proof admission;
  they fix the forms a contract takes and the constants it may not reach, nothing of what it states.
  How the clause is proved is the answer's; that it stands is checked.
\<close>

ML \<open>
structure Development_Verification_Frame =
struct

(*Part (c): the bootstrap loop's presentation relations and datatypes, by name, as task 381's entry
  lists them (the development_problem datatype, the Isabelle state datatypes, task 9's rows, loci,
  prefixes and keys, readiness_presents, state_presents, request_presents, development_rows_present),
  with those of Isabelle_Type_Tables, Isabelle_Local_Names and Isabelle_Code_Equations that its
  criterion takes, the row citation presenters of Development_Row_Data and the key agreement of
  presented states. A native program defined in the same theories is not listed.*)
val bootstrap_constants =
  ["Development_Native_Selection.readiness_presents",
   "Development_State_Rows.state_presents", "Development_State_Rows.rows_present",
   "Development_State_Rows.atoms_present", "Development_State_Rows.roots_present",
   "Development_State_Rows.presented_rows", "Development_State_Rows.entity_row",
   "Development_State_Rows.root_row",
   "Development_Request_Keys.request_presents",
   "Development_Rows.development_rows_present", "Development_Rows.development_problems_present",
   "Development_Rows.development_requests_present", "Development_Rows.development_issues_present",
   "Development_Loci.development_locus", "Development_Loci.development_role_path",
   "Development_Loci.development_kind_path",
   "Development_Entity_Keys.first_occurrence_key", "Development_Entity_Keys.development_entity_key",
   "Development_State_Presenter.state_constant_key",
   "Isabelle_Type_Tables.isabelle_type_table",
   "Isabelle_Local_Names.isabelle_local_names", "Isabelle_Local_Names.isabelle_local_embedding",
   "Isabelle_Code_Equations.isabelle_code_equation_proposition",
   "Isabelle_Code_Equations.isabelle_definition_proposition",
   "Development_Row_Data.development_citation_data", "Development_Row_Data.development_citations_data",
   "Development_State_Rows.keyed_agree", "Development_State_Rows.keys_shared"];

val bootstrap_types =
  ["Development_Problems.development_problem", "Development_Problems.development_contract",
   "Development_Problems.development_origin", "Development_Problems.development_authority",
   "Isabelle_Terms.isabelle_type", "Isabelle_Terms.isabelle_term_with",
   "Isabelle_Entities.isabelle_entity_with", "Isabelle_Type_Tables.isabelle_type_node",
   "Development_State_Rows.entity_kind", "Development_State_Rows.state_row.state_row_ext",
   "Development_State_Rows.state_rows.state_rows_ext", "Development_Loci.development_role"];

val store_theories =
  ["Binary_Path_Stores", "Binary_Relation_Stores", "Binary_Nested_Stores", "Native_Path_Stores",
   "RBT", "RBT_Impl"];

fun home name = hd (Long_Name.explode name);

fun add_type_constructors (Type (a, Ts)) = insert (op =) a #> fold add_type_constructors Ts
  | add_type_constructors _ = I;

(*Every type constructor a type constructor's definition reaches: datatype constructors' argument
  types, a type definition's representation type.*)
fun type_closure ctxt names =
  let
    fun defined name =
      (case Ctr_Sugar.ctr_sugar_of ctxt name of
        SOME {ctrs, ...} => fold (fold_types add_type_constructors) ctrs []
      | NONE =>
          (case Typedef.get_info ctxt name of
            ({rep_type, ...}, _) :: _ => add_type_constructors rep_type []
          | [] => []));
    fun walk [] seen = seen
      | walk (n :: rest) seen =
          if member (op =) seen n then walk rest seen else walk (defined n @ rest) (n :: seen);
  in walk names [] end;

val use_type = \<^typ>\<open>local_address option\<close>;

(*The use actions the use instance states, each with its notion's subject type and the presenter
  its notion's classes are built from.*)
val use_actions =
  [(@{thm Factor_Use_Actions.environment_renaming_action},
     \<^typ>\<open>local_address option artifact_environment\<close>, \<^const_name>\<open>environment_value_presents\<close>),
   (@{thm Factor_Use_Renaming.site_context_renaming_action}, \<^typ>\<open>site_context\<close>,
     \<^const_name>\<open>site_value_presents\<close>),
   (@{thm Factor_Use_Renaming.program_entry_renaming_action}, \<^typ>\<open>program_entry_context\<close>,
     \<^const_name>\<open>program_entry_value_presents\<close>),
   (@{thm Factor_Use_Actions.site_renaming_action}, \<^typ>\<open>local_address option \<times> local_address\<close>,
     \<^const_name>\<open>site_data_term\<close>),
   (@{thm Factor_Use_Actions.use_renaming_action}, use_type, \<^const_name>\<open>use_data_term\<close>)];

(*The notion's trivial action, stated once in Presentation_Equivariance.*)
val trivial_action = @{thm Presentation_Equivariance.permutation_renaming_action};

(*The type constructors of exact values, which hold no use by their definitions.*)
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

exception Underived of string;

fun refuse entry msg =
  error ("The verification frame refuses the theory at the entry " ^ entry ^ ": " ^ msg);

fun instances thy loc morph =
  map (fn ((x, T), _) => (x, Morphism.term morph (Free (x, T)))) (Locale.params_of thy loc);

fun registrations thy name =
  let val loc = Locale.intern thy name
  in map (instances thy loc o snd) (Locale.registrations_of (Context.Theory thy) loc) end;

fun param ps x = the (AList.lookup (op =) ps x);

fun mentions c t = member (op =) (Term.add_const_names t []) c;

fun closed t = not (loose_bvar (t, 0));

(*The action a use-instance theorem states, instantiated at the class's domain.*)
fun action_of thy D th =
  let
    val (adm, act, dom) =
      (case HOLogic.dest_Trueprop (Thm.concl_of th) of
        _ $ adm $ act $ dom => (adm, act, dom)
      | t => raise TERM ("action_of", [t]));
    val tyenv = Sign.typ_match thy (fastype_of dom, fastype_of D) Vartab.empty;
  in
    if Envir.subst_type tyenv (fastype_of adm) = (use_type --> use_type) --> HOLogic.boolT andalso
      Envir.beta_eta_contract (Envir.subst_term_types tyenv dom) aconv Envir.beta_eta_contract D
    then SOME (Envir.subst_term_types tyenv act) else NONE
  end handle Type.TYPE_MATCH => NONE;

fun trivial_of thy T =
  let
    val (adm, act, dom) =
      (case HOLogic.dest_Trueprop (Thm.concl_of trivial_action) of
        _ $ adm $ act $ dom => (adm, act, dom)
      | t => raise TERM ("trivial_of", [t]));
    val tyenv = Vartab.empty
      |> Sign.typ_match thy (fastype_of dom, T --> HOLogic.boolT)
      |> Sign.typ_match thy (fastype_of adm, (use_type --> use_type) --> HOLogic.boolT);
  in Envir.subst_term_types tyenv act end;

(*The side of a product's body that reads its bound variables only through the projection sel,
  abstracted over the variables it reads: frees pairs each bound index with its variable.*)
fun side sel frees body =
  let
    fun replace d (t as Const (s, _) $ Bound i) =
          if s = sel then (case AList.lookup (op =) frees (i - d) of SOME v => v | NONE => t) else t
      | replace d (f $ x) = replace d f $ replace d x
      | replace d (Abs (n, T, b)) = Abs (n, T, replace (d + 1) b)
      | replace _ t = t;
    val t = replace 0 body;
  in
    if loose_bvar (t, 0) then NONE
    else SOME (Envir.beta_eta_contract (fold_rev (fn (_, v) => Term.lambda v) frees t))
  end;

fun lifted construction act =
  Abs ("h", use_type --> use_type, Const (construction, dummyT) $ (act $ Bound 0));

(*The context a derivation reads: the theory, this theory's own facts and the presentation classes
  registered or stated in it.*)
type frame = {thy: theory, ctxt: Proof.context, facts: thm list, classes: (term * term) list};

fun stands ({thy, facts, ...}: frame) clause =
  exists (fn th => Thm.nprems_of th = 0 andalso
    Pattern.matches thy (Envir.beta_eta_contract (Thm.prop_of th), clause)) facts;

fun class_domain ({classes, ...}: frame) R =
  Option.map snd (find_first (fn (R', _) => Envir.beta_eta_contract R' aconv Envir.beta_eta_contract R) classes);

fun string_of ({ctxt, ...}: frame) t = Syntax.string_of_term ctxt t;

(*The use action a class derives from its construction, or Underived.*)
fun derive (frame as {thy, ...}: frame) (R, D) =
  let
    val T = domain_type (fastype_of D);
    val R' = Envir.beta_eta_contract R;
    val D' = Envir.beta_eta_contract D;
    fun underived () =
      raise Underived ("no use action derives for the class " ^ string_of frame R ^
        " over the domain " ^ string_of frame D);
    fun lift construction r0 d0 =
      if closed r0 andalso closed d0 then lifted construction (derive frame (r0, d0)) else underived ();
    fun product (r1, d1) (r2, d2) =
      Const (\<^const_name>\<open>product_action\<close>, dummyT) $ derive frame (r1, d1) $ derive frame (r2, d2);
    fun domain_components T1 T2 =
      (case D' of
        Abs (_, _, Const (\<^const_name>\<open>conj\<close>, _) $ l $ r) =>
          (case (side \<^const_name>\<open>fst\<close> [(0, Free ("a", T1))] l,
              side \<^const_name>\<open>snd\<close> [(0, Free ("a", T2))] r) of
            (SOME d1, SOME d2) => SOME (d1, d2)
          | _ => NONE)
      | Abs (_, _, Const (\<^const_name>\<open>True\<close>, _)) =>
          SOME (Abs ("x", T1, \<^const>\<open>True\<close>), Abs ("x", T2, \<^const>\<open>True\<close>))
      | _ => NONE);
    (*A product class: its body a conjunction of two sides, each reading the subject and the
      presentation only through one projection.*)
    fun product_class () =
      (case (R', T) of
        (Abs (_, _, Abs (_, Type (\<^type_name>\<open>prod\<close>, [P1, P2]), Const (\<^const_name>\<open>conj\<close>, _) $ x $ y)),
         Type (\<^type_name>\<open>prod\<close>, [T1, T2])) =>
          (case (side \<^const_name>\<open>fst\<close> [(1, Free ("a", T1)), (0, Free ("q", P1))] x,
              side \<^const_name>\<open>snd\<close> [(1, Free ("a", T2)), (0, Free ("q", P2))] y,
              domain_components T1 T2) of
            (SOME r1, SOME r2, SOME (d1, d2)) => SOME (product (r1, d1) (r2, d2))
          | _ => NONE)
      | _ => NONE);
    fun base () =
      (case get_first (fn (th, subject, presenter) =>
          if T = subject andalso mentions presenter R' then action_of thy D th else NONE) use_actions of
        SOME act => act
      | NONE =>
          if use_free T orelse
            (T = use_type andalso mentions \<^const_name>\<open>optional_payload_term\<close> R' andalso
              not (mentions \<^const_name>\<open>use_data_term\<close> R'))
          then trivial_of thy T
          else underived ());
    fun subdomain () = subdomain_of frame (R, D) base;
  in
    (case R' of
      Const (\<^const_name>\<open>list_all2\<close>, _) $ r0 =>
        (case D' of
          Abs (_, _, Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>set\<close>, _) $ Bound 0) $ d0) =>
            lift \<^const_name>\<open>map\<close> r0 d0
        | _ => underived ())
    | Const (\<^const_name>\<open>data_sequence_presents\<close>, _) $ r0 =>
        (case D' of
          Abs (_, _, Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>set\<close>, _) $ Bound 0) $ d0) =>
            lift \<^const_name>\<open>map\<close> r0 d0
        | _ => underived ())
    | Const (\<^const_name>\<open>data_collection_presents\<close>, _) $ r0 =>
        (case D' of
          Abs (_, _, Const (\<^const_name>\<open>conj\<close>, _) $ (Const (\<^const_name>\<open>finite\<close>, _) $ Bound 0) $
            (Const (\<^const_name>\<open>Ball\<close>, _) $ Bound 0 $ d0)) => lift \<^const_name>\<open>image\<close> r0 d0
        | _ => underived ())
    | Abs (_, _, Abs (_, _, Const (\<^const_name>\<open>data_collection_presents\<close>, _) $ r0 $
        (Const (\<^const_name>\<open>fset\<close>, _) $ Bound 1) $ Bound 0)) =>
        (case D' of
          Abs (_, _, Const (\<^const_name>\<open>Ball\<close>, _) $ (Const (\<^const_name>\<open>fset\<close>, _) $ Bound 0) $ d0) =>
            lift \<^const_name>\<open>fimage\<close> r0 d0
        | _ => underived ())
    | Const (\<^const_name>\<open>composed_presentation\<close>, _) $ r0 $ _ => derive frame (r0, D)
    | Abs (_, _, Abs (_, _, Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _)) =>
        (case product_class () of SOME act => act | NONE => subdomain ())
    | _ => base ())
  end
and subdomain_of (frame as {ctxt, ...}: frame) (R, D) base =
    (case (Envir.beta_eta_contract R, Envir.beta_eta_contract D) of
      (Abs (_, _, Abs (_, _, Const (\<^const_name>\<open>conj\<close>, _) $ (e $ Bound 1) $ (r0 $ Bound 1 $ Bound 0))), D') =>
        if closed e andalso closed r0 andalso e aconv D' then
          (case class_domain frame r0 of
            SOME D0 =>
              let
                val act = derive frame (r0, D0);
                val restriction = Syntax.check_term ctxt (HOLogic.mk_Trueprop
                  (Const (\<^const_name>\<open>renaming_action\<close>, dummyT) $ Syntax.parse_term ctxt "bij" $
                    act $ D)) |> Envir.beta_eta_contract;
              in
                if stands frame restriction then act
                else raise Underived ("the subdomain class " ^ string_of frame R ^
                  " needs its action restricted, as this theory states no theorem " ^
                  string_of frame restriction)
              end
          | NONE => base ())
        else base ()
    | _ => base ());

fun derivable thy (R, D) =
  let
    val frame = {thy = thy, ctxt = Proof_Context.init_global thy, facts = [], classes = []};
  in SOME (derive frame (R, D)) handle Underived _ => NONE end;

fun own_facts thy =
  Facts.dest_static false (map Global_Theory.facts_of (Theory.parents_of thy))
    (Global_Theory.facts_of thy)
  |> maps snd;

fun concl_head th =
  (case HOLogic.dest_Trueprop (Logic.strip_imp_concl (Thm.prop_of th)) of
    t => (case Term.strip_comb t of (Const (c, _), args) => SOME (c, args) | _ => NONE))
  handle TERM _ => NONE;

(*Part (f). A store operation is a constant of the store theories other than a store's constructor; a
  store search is an application of one to its arguments, maximal in the term it stands in.*)
fun store_constant c = member (op =) store_theories (home c);

fun constructor thy c =
  (case body_type (Sign.the_const_type thy c) of
    Type (a, _) =>
      (case Ctr_Sugar.ctr_sugar_of (Proof_Context.init_global thy) a of
        SOME {ctrs, ...} => exists (fn t => fst (dest_Const t) = c) ctrs
      | NONE => false)
  | _ => false)
  handle TYPE _ => false;

fun store_applications thy =
  let
    fun walk u =
      (case strip_comb u of
        (Const (c, _), args) =>
          if not (store_constant c) orelse constructor thy c then fold walk args
          else insert (op aconv) u
      | (Abs (_, _, b), args) => walk b #> fold walk args
      | (_, args) => fold walk args);
  in walk end;

fun reach definitions seeds =
  Isabelle_Constant_Closure.closure definitions (fn t => Term.add_const_names t [])
    (fold Term.add_const_names seeds []);

(*The store searches a closure reaches: in its seeds and in the definitions it selects outside the
  stores (a store operation defined by another is the stores' own, not a search reached).*)
fun reached_applications thy seeds selected =
  fold (store_applications thy)
    (seeds @ map snd (filter_out (store_constant o fst) (Symtab.dest selected))) [];

fun ground t =
  not (null (snd (strip_comb t))) andalso not (loose_bvar (t, 0)) andalso
  null (Term.add_frees t []) andalso null (Term.add_vars t []);

(*The store operations a search applies: its head and every store operation within its arguments.*)
fun store_operations thy t =
  filter (fn c => store_constant c andalso not (constructor thy c)) (Term.add_const_names t []);

(*Carrier indexes stated as theorems anywhere in the context, possibly under premises, each an
  instance: its build, search, site and index term hold no schematic variable, so a locale's generic
  statement (native_store_search_program.index) never counts. Each is named with its anchors (site and
  checker) and its stated operations (build, search, key presentation).*)
fun index_theorems thy =
  Facts.fold_static (fn (name, ths) => fold (fn th =>
    (case concl_head th of
      SOME (c, args) =>
        if c = \<^const_name>\<open>native_carrier_index\<close> andalso length args = 11 then
          if exists (Term.exists_subterm is_Var) (map (nth args) [4, 5, 6, 9]) then I
          else
            cons (name, filter_out (Term.exists_subterm is_Var) (map (nth args) [6, 10]),
              filter_out (Term.exists_subterm is_Var) (map (nth args) [4, 5, 8]), name)
        else I
    | NONE => I)) ths) (Global_Theory.facts_of thy) [];

(*Native_Path_Store_Indexes states the carrier index of every interpretation of the path store's search
  program (native_store_search_program.index, under the formation of its values) in the program's
  context, so an interpretation made where that statement stands is a carrier index instance: its
  anchors are its parameters (the program its site reads and the two sites), its stated operations the
  build, search and key presentation of that statement.*)
fun search_program_indexes thy =
  (case try (Global_Theory.get_thms thy) "Native_Path_Store_Indexes.native_store_search_program.index" of
    SOME (th :: _) =>
      let
        val args = (case concl_head th of SOME (_, args) => args | NONE => []);
        val stated =
          if length args = 11 then filter_out (Term.exists_subterm is_Var) (map (nth args) [4, 5, 8]) else [];
      in
        map (fn ps => ("native_store_search_program.index at the interpretation of " ^
            commas (map (Syntax.string_of_term_global thy o snd) ps), map snd ps, stated,
            "native_store_search_program.index"))
          (registrations thy "native_store_search_program")
      end
  | _ => []);

fun registered_indexes thy =
  map (fn ps =>
    let val name = "a registration with the site " ^ Syntax.string_of_term_global thy (param ps "site")
    in
      (name, map_filter (AList.lookup (op =) ps) ["site", "checker"],
        map_filter (AList.lookup (op =) ps) ["build", "search", "present"], name)
    end) (registrations thy "native_carrier_index");

(*An index with what it searches: its own searches, the closed store searches its anchors reach whose
  arguments all stand in its anchors; and its operations, the store operations its stated build,
  search and key presentation apply. A search at open arguments is matched when every store operation
  it applies is among one index's operations, so the store it searches, where it stands on the text, is
  built by the index's build; where the store is a variable, its carrier is not read.*)
fun index_record thy definitions (name, anchors, stated, stated_name) =
  let
    fun inside x = exists (Term.exists_subterm (fn u => u aconv x)) anchors;
    val own =
      filter (fn t => ground t andalso forall inside (snd (strip_comb t)))
        (reached_applications thy anchors (snd (reach definitions anchors)));
    val operations = fold (union (op =) o store_operations thy) stated [];
  in (name, own, operations, stated_name) end;

fun carrier_indexes thy definitions =
  map (index_record thy definitions)
    (registered_indexes thy @ index_theorems thy @ search_program_indexes thy);

(*The given's package program: the store searches it reaches are the given's, not an answer's.*)
val given_programs = ["Development_Package_Program.package_program"];

fun given_applications thy definitions =
  let
    val seeds =
      map_filter (fn c => Option.map (fn T => Const (c, T)) (try (Sign.the_const_type thy) c))
        given_programs;
  in if null seeds then [] else reached_applications thy seeds (snd (reach definitions seeds)) end;

fun equivariance_clause ctxt act D P =
  Syntax.check_term ctxt (HOLogic.mk_Trueprop
    (Const (\<^const_name>\<open>renaming_equivariant\<close>, dummyT) $ Syntax.parse_term ctxt "bij" $ act $ D $ P))
  |> Envir.beta_eta_contract;

fun check thy program entries =
  let
    val ctxt = Proof_Context.init_global thy;
    val P = Syntax.read_term ctxt program;
    val facts = own_facts thy;
    val class_facts =
      map_filter (fn th =>
        if Thm.nprems_of th = 0 then
          (case concl_head th of
            SOME (c, [R, D, _]) => if c = \<^const_name>\<open>presentation_class\<close> then SOME (R, D) else NONE
          | _ => NONE)
        else NONE) facts;
    val classes =
      map (fn ps => (param ps "presents", param ps "subject")) (registrations thy "presentation_class")
      @ class_facts;
    val frame = {thy = thy, ctxt = ctxt, facts = facts, classes = classes};
    val contracts = registrations thy "presented_relation_contract";
    val definitions = Isabelle_Constant_Closure.kernel_definitions thy;
    (*The context's carrier indexes and the given's searches, computed once for the whole check.*)
    val indexes = Lazy.lazy (fn () => carrier_indexes thy definitions);
    val given = Lazy.lazy (fn () => given_applications thy definitions);
    fun reached seeds =
      let
        val (seen, selected) = reach definitions seeds;
        val types = fold (fold_types add_type_constructors) (seeds @ map snd (Symtab.dest selected)) [];
      in
        (sort_strings (Symtab.keys seen), sort_strings (type_closure ctxt types),
          reached_applications thy seeds selected)
      end;
    fun statement_checks entry seeds =
      let
        val (constants, types, applications) = reached seeds;
        val bad_constants = filter (member (op =) bootstrap_constants) constants;
        val bad_types = filter (member (op =) bootstrap_types) types;
        val _ =
          if null bad_constants andalso null bad_types then ()
          else refuse entry ("its contract's statement reaches, through the shared constant " ^
            "closure and the type definitions, the bootstrap loop's presentations: the constants " ^
            commas bad_constants ^ "; the types " ^ commas bad_types);
        val show = Syntax.string_of_term ctxt;
        fun matches t (_, own, operations, _) =
          if ground t then member (op aconv) own t
          else subset (op =) (store_operations thy t, operations);
        fun place t =
          (case find_first (matches t) (Lazy.force indexes) of
            SOME (name, _, _, stated_name) =>
              (NONE, SOME ("the store search " ^ show t ^
                (if ground t then " is the own search of the carrier index " ^ name
                 else " applies only operations stated by the carrier index " ^ stated_name)))
          | NONE =>
              if member (op aconv) (Lazy.force given) t
              then (NONE, SOME ("the given's store search " ^ show t ^ " has no carrier index of its own"))
              else (SOME t, NONE));
        val placed = map place applications;
        val unmatched = map_filter fst placed;
      in
        if null unmatched then
          List.app (fn (_, SOME msg) => writeln ("Part (f) at the entry " ^ entry ^ ": " ^ msg) | _ => ())
            placed
        else refuse entry ("its contract relies on the store searches " ^
          commas (map (fn t => show t ^ (if ground t then "" else
            " (its store operations " ^ commas (store_operations thy t) ^ ")")) unmatched) ^
          ", and no carrier index instance (native_carrier_index), registered, stated as a theorem or as " ^
          "native_store_search_program.index at an interpretation of the search program, has it as its " ^
          "own search: every store an answer adds needs an index of its own")
      end;
    fun action entry (R, D) =
      derive frame (R, D) handle Underived msg => refuse entry msg;
    fun binary_observation d =
      Syntax.check_term ctxt (Abs ("p", dummyT, Abs ("q", dummyT,
        Const (\<^const_name>\<open>Set.member\<close>, dummyT) $
          (Const (\<^const_name>\<open>Pair\<close>, dummyT) $ d $
            (Const (\<^const_name>\<open>Pair_Term\<close>, dummyT) $ Bound 1 $ Bound 0)) $
          (Const (\<^const_name>\<open>positive_meaning\<close>, dummyT) $ P))))
      |> Envir.beta_eta_contract;
    fun unary_observation d =
      Syntax.check_term ctxt (Abs ("p", dummyT,
        Const (\<^const_name>\<open>Set.member\<close>, dummyT) $ (Const (\<^const_name>\<open>Pair\<close>, dummyT) $ d $ Bound 0) $
          (Const (\<^const_name>\<open>positive_meaning\<close>, dummyT) $ P)))
      |> Envir.beta_eta_contract;
    fun unary_form expected th =
      if Thm.nprems_of th <> 0 then NONE
      else
        (case HOLogic.dest_Trueprop (Thm.prop_of th) of
          Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $
            (Const (\<^const_name>\<open>presented_predicate\<close>, _) $ R $ Q $ (x as Var _)) =>
              if Envir.beta_eta_contract (Term.lambda x lhs) aconv expected then SOME (R, Q) else NONE
        | _ => NONE)
        handle TERM _ => NONE;
    fun check_binary entry ps =
      let
        val _ = statement_checks entry (map snd ps);
        val D = param ps "D";
        val E = param ps "E";
        val fst_z = Const (\<^const_name>\<open>fst\<close>, dummyT) $ Bound 0;
        val snd_z = Const (\<^const_name>\<open>snd\<close>, dummyT) $ Bound 0;
        val clause = equivariance_clause ctxt
          (Const (\<^const_name>\<open>product_action\<close>, dummyT) $ action entry (param ps "R", D) $
            action entry (param ps "S", E))
          (Abs ("z", dummyT, Const (\<^const_name>\<open>conj\<close>, dummyT) $ (D $ fst_z) $ (E $ snd_z)))
          (Abs ("z", dummyT, param ps "relation" $ fst_z $ snd_z));
      in
        if stands frame clause then ()
        else refuse entry ("no theorem of this theory states its use equivariance clause " ^
          Syntax.string_of_term ctxt clause)
      end;
    fun check_unary entry (R, Q) =
      (case class_domain frame R of
        NONE => refuse entry ("its predicate's class " ^ Syntax.string_of_term ctxt R ^
          " is no presentation class registered or stated in this theory")
      | SOME D =>
          let
            val _ = statement_checks entry [R, D, Q, P];
            val clause = equivariance_clause ctxt (action entry (R, D)) D Q;
          in
            if stands frame clause then ()
            else refuse entry ("no theorem of this theory states its use equivariance clause " ^
              Syntax.string_of_term ctxt clause)
          end);
    fun check_entry entry =
      let
        val d = Syntax.parse_term ctxt entry;
        val binary = binary_observation d;
        val found =
          filter (fn ps => Envir.beta_eta_contract (param ps "observe") aconv binary) contracts;
      in
        if not (null found) then List.app (check_binary entry) found
        else
          (case map_filter (unary_form (unary_observation d)) facts of
            [] => refuse entry ("no interpretation of presented_relation_contract or " ^
              "presented_function_contract states a contract whose observation is " ^
              Syntax.string_of_term ctxt binary ^ ", and no theorem of this theory states " ^
              Syntax.string_of_term ctxt (unary_observation d) ^ " as a presented predicate")
          | unary => List.app (check_unary entry) unary)
      end;
    val _ = List.app check_entry entries;
  in
    writeln ("The verification frame accepts the entries " ^ commas entries ^ " of " ^
      Syntax.string_of_term ctxt P)
  end;

end
\<close>

end
