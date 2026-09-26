theory Development_Socket_Liveness_Execution
  imports Development_First_Problem_Asked Development_Given_Carried_Declarations
    Factor_Schema_Instantiation_Declarations Factor_Union_Declarations Factor_Definition_Reading_Declarations
    Factor_Stated_Leaves_Program Native_Execution_Refinements
begin

text \<open>
  The liveness of every declared socket over the asked program (B3b of correction (10) of DECISIONS.md "Committed
  choice, for refusals", review 726's follow-up 2), read from the clauses and the records, in a thin theory that no
  library theory imports. It decides nothing for the route: it reads the test's conditions the clauses decide, at
  every clause of the asked program calling a socket's parent site, today (the default frame and the variant test)
  and after (the default or a declared frame, and (iii) at a declared frame).

  How the clauses are read. A socket (e,S,s,keep,Vp,Vh) and a caller premise (k,e,p) of a clause S' at site f: the
  parent's head is unified with the caller's pattern, the two renamed apart (@{const finite_unify_patterns}); a head
  variable's binding is its image under the unifier. The head's input at Vh and the head outputs the caller fixes to
  a ground pattern are ground at the start. A socket input (@{const finite_socket_inputs}) not ground at the start is
  fed by the siblings that hold it: those a producer the records declare at their site reads at a view with the
  variable in its output, their view's input then needed in turn; where no view produces it, the first sibling in key
  order holding it and read by no view with the variable in its input (closed by the search, grounding all its
  variables; a material premise needs its source). The siblings feeding the inputs, closed backward, are the siblings
  closed before the socket's
  input is ground; a variable no sibling holds leaves the input never ground. Conditions (i) and (ii) read those
  siblings' variables and the ground premise-only variables against the frame. The parent node's call is its head
  under the binding, a head variable the start holds ground counting as ground; today the head's output at Vh is a
  variant of that call's output there (@{const finite_parent_output}), after (iii) holds at the choice's frame, the
  default frame at the default choice (@{const finite_parent_absorbs}'s conditions on the static binding); the call's
  input apart from its output and a socket output left with a variable once the head is bound stand at both.

  The parent is committed at a caller directly (a producer declared at e reads the call with an output, the view's
  input is fed in the caller's clause from its head input at the views declared at its site, its whole head where
  none is, and every other premise of the caller's clause holding an output variable is a declared consumer of it
  (@{const finite_output_consumer}'s condition; a material premise never) or at the caller's premise when it is itself
  a declared socket live there. Where the output's variables reach the caller's head, goals outside the clause may
  hold them and the clause does not decide the consumers (the runtime test decides at the goals present, correction
  (11)). Three readings count such a commitment: strictly never; focused where the caller's site is itself committed
  (directly at its own caller, or as the goal of a live socket, kept or free), the caller's node then the root of the
  committed sub-search and its clause deciding; leniently always. Liveness is a joint least fixpoint over committed
  sites and live sockets. A kept socket needs no committed parent. Only callers in a clause the asked relation's entry
  526 reaches are read (the route, below); a socket whose parent no such clause calls is named off the route.
  What the evaluation cannot read it does not guess: the order the search takes goals, and a caller variable ground
  by the caller's own earlier premises beyond what its clause shows.
\<close>

text \<open>
  The records' clauses are written with @{const finite_pattern_of}, whose target case reads an artifact's finite
  presentation by a description; no socket clause holds a target, so that case aborts here and is never reached.
\<close>

text \<open>
  #609's narrowed sockets are read as their sockets: the record's truncation
  (@{const resolution_declarations.truncate}, @{thm [source] narrowed_truncate}), without its class, which the evaluation
  never reads (whether a production applies at them is not read here); the class aborts in code.
\<close>

declare [[code abort: finite_object_of union_class]]


definition liveness_declarations :: "(nat,nat,nat) resolution_declarations" where
  "liveness_declarations = declarations_list ([given_declarations, quotation_declarations, binding_declarations,
    instantiation_declarations, scoped_declarations, prospective_declarations, application_declarations,
    row_values_declarations, vector_declarations, record_declarations, material_declarations,
    premise_rows_declarations, premise_family_declarations, schema_declarations] @
    map (resolution_declarations.truncate \<circ> union_narrowed) [quotation_union_sockets, instantiation_union_sockets,
      prospective_union_sockets, vector_union_sockets, premise_rows_union_sockets] @
    [call_admission_declarations, clause_payloads_declarations, interface_slot_declarations,
      stated_clause_declarations])"

definition liveness_frames :: "(nat,nat,nat) resolution_frames" where
  "liveness_frames = lookup_frames |\<union>| identity_frames |\<union>| comparison_frames |\<union>| headed_frames |\<union>|
    family_rows_frames |\<union>| admission_frames |\<union>| interpretation_frames |\<union>| binder_frames |\<union>| quotation_frames |\<union>|
    instantiation_frames |\<union>| prospective_frames |\<union>| application_frames |\<union>| vector_frames |\<union>| record_frames |\<union>|
    material_frames |\<union>| premise_rows_frames |\<union>| premise_family_frames |\<union>| schema_frames |\<union>|
    schema_family_socket_frames |\<union>| callee_inclusion_socket_frames |\<union>| payload_audit_socket_frames |\<union>|
    clause_reading_row_frames |\<union>| premise_slot_row_frames |\<union>| schema_slot_row_frames |\<union>| root_slot_row_frames |\<union>|
    quotation_union_frames |\<union>| instantiation_union_frames |\<union>| prospective_union_frames |\<union>| vector_union_frames |\<union>|
    premise_rows_union_frames |\<union>| interface_slot_frames |\<union>| stated_clause_frames"

type_synonym liveness_socket =
  "nat \<times> (nat,nat,nat) finite_factor_schema \<times> nat \<times> bool \<times> nat resolution_view \<times> nat resolution_view"

type_synonym liveness_caller = "nat \<times> nat \<times> (nat,nat,nat) finite_factor_schema \<times> nat \<times> nat finite_term_pattern"

section \<open>The callers and the parent's bindings\<close>

definition liveness_callers ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> liveness_caller fset" where
  "liveness_callers P e = ffUnion ((\<lambda>((f,c),S'). (\<lambda>(k,d,p). (f,c,S',k,p)) |`|
      ffilter (\<lambda>(k,d,p). d = e) (finite_schema_premises S')) |`| finite_system_clauses P)"

text \<open>The route: the sites the asked relation's entry 526 reaches; a caller counts only in a clause at one of them.\<close>

definition liveness_route :: "nat fset" where
  "liveness_route = finite_definition_closure finite_asked_program {|526|}"

definition liveness_route_callers ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat fset \<Rightarrow> nat \<Rightarrow> liveness_caller fset" where
  "liveness_route_callers P R e = ffilter (\<lambda>(f,cc,S',k,p). f |\<in>| R) (liveness_callers P e)"

definition liveness_unifier ::
    "(nat,nat,nat) finite_factor_schema \<Rightarrow> nat finite_term_pattern \<Rightarrow> ((bool \<times> nat) \<times> (bool \<times> nat) finite_term_pattern) list option" where
  "liveness_unifier S p = finite_unify_patterns (finite_rename_apart True (finite_schema_conclusion S))
    (finite_rename_apart False p)"

definition liveness_binding ::
    "((bool \<times> nat) \<times> (bool \<times> nat) finite_term_pattern) list \<Rightarrow> nat \<Rightarrow> (bool \<times> nat) finite_term_pattern" where
  "liveness_binding u a = finite_binding_substitution u (True,a)"

section \<open>The siblings closed before an input is ground\<close>

text \<open>
  A feeder of a variable at a key's siblings is a row (key, the variables it needs, all its variables): a call premise a
  producer's view reads with the variable in its output, or, where none does, the first premise in key order holding it
  and not reading it as a view's input: a call premise (needing nothing) or a material premise (needing its source).
\<close>

definition liveness_first :: "(nat \<times> nat fset \<times> nat fset) fset \<Rightarrow> (nat \<times> nat fset \<times> nat fset) fset" where
  "liveness_first R = (if R = {||} then {||} else ffilter (\<lambda>(q,i,w). q = fMin ((\<lambda>(q,i,w). q) |`| R)) R)"

definition liveness_feeders ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> (nat,nat,nat) finite_factor_schema \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      (nat \<times> nat fset \<times> nat fset) fset" where
  "liveness_feeders D S s v = (let
      calls = ffilter (\<lambda>(q,d,p). q \<noteq> s \<and> v |\<in>| finite_pattern_variables p \<and>
          \<not> fBex (declared_producers D) (\<lambda>(d',V,hs). d' = d \<and> (case resolution_view_pattern V p of None \<Rightarrow> False
            | Some (x,y) \<Rightarrow> v |\<in>| finite_pattern_variables x)))
        (finite_schema_premises S);
      viewing = ffilter (\<lambda>(q,d,p). q \<noteq> s \<and> v |\<in>| finite_pattern_variables p) (finite_schema_premises S);
      viewed = ffUnion ((\<lambda>(q,d,p). ffUnion ((\<lambda>(d',V,hs). case resolution_view_pattern V p of None \<Rightarrow> {||}
          | Some (x,y) \<Rightarrow> if v |\<in>| finite_pattern_variables p |-| finite_pattern_variables x
              then {|(q,finite_pattern_variables x,finite_pattern_variables p)|} else {||})
        |`| ffilter (\<lambda>(d',V,hs). d' = d) (declared_producers D))) |`| viewing)
    in if viewed \<noteq> {||} then viewed
      else liveness_first ((\<lambda>(q,d,p). (q,{||},finite_pattern_variables p)) |`| calls |\<union>|
        (\<lambda>(q,N). (q,finite_pattern_variables (finite_material_source N),finite_material_variables N)) |`|
          ffilter (\<lambda>(q,N). q \<noteq> s \<and> v |\<in>| finite_material_variables N) (finite_schema_materials S)))"

definition liveness_need ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> (nat,nat,nat) finite_factor_schema \<Rightarrow> nat \<Rightarrow> nat fset \<Rightarrow>
      nat fset \<Rightarrow> (nat \<times> nat fset \<times> nat fset) fset option" where
  "liveness_need D S s G0 I = (let
      grow = (\<lambda>N. N |\<union>| ffUnion ((\<lambda>v. ffUnion ((\<lambda>(q,i,w). i) |`| liveness_feeders D S s v)) |`| (N |-| G0)));
      N = (grow ^^ Suc (fcard (finite_schema_variables S))) (I |-| G0)
    in if fBall (N |-| G0) (\<lambda>v. liveness_feeders D S s v \<noteq> {||})
      then Some (ffUnion ((\<lambda>v. liveness_feeders D S s v) |`| (N |-| G0))) else None)"

text \<open>
  The head inputs of a clause at its site: at every producer view and socket head view declared there; its whole
  head where none is declared.
\<close>

definition liveness_head_inputs ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) finite_factor_schema \<Rightarrow> nat fset" where
  "liveness_head_inputs D f S = (let Vs = (\<lambda>(d,V,hs). V) |`| ffilter (\<lambda>(d,V,hs). d = f) (declared_producers D) |\<union>|
      (\<lambda>(e,S',s,keep,Vp,Vh). Vh) |`| ffilter (\<lambda>(e,S',s,keep,Vp,Vh). e = f \<and> S' = S) (declared_sockets D)
    in if Vs = {||} then finite_pattern_variables (finite_schema_conclusion S)
      else ffUnion ((\<lambda>V. case resolution_view_pattern V (finite_schema_conclusion S) of
        Some (x,y) \<Rightarrow> finite_pattern_variables x | None \<Rightarrow> {||}) |`| Vs))"

section \<open>The conditions at one caller\<close>

text \<open>
  At a frame choice (@{term None} the default frame, @{term "Some C"} a declared frame): the input ground, (i) the
  feeding siblings' variables outside the frame, (ii) the ground premise-only variables outside it, and at a free
  socket the parent's call: the variant test today, (iii) at the frame after.
\<close>

record liveness_reading =
  reading_matched :: bool
  reading_ground :: bool
  reading_closed :: "nat fset"
  reading_children :: bool
  reading_premise_only :: bool
  reading_outputs :: bool

definition liveness_read ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> liveness_socket \<Rightarrow> bool \<Rightarrow> nat fset option \<Rightarrow> liveness_caller \<Rightarrow>
      liveness_reading" where
  "liveness_read D \<sigma> after ch c = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow> case c of (f,cc,S',k,p) \<Rightarrow>
    let C = (case ch of None \<Rightarrow> finite_default_frame Vp Vh S s | Some C \<Rightarrow> C);
        I = finite_socket_inputs Vp Vh S s;
        PO = finite_schema_variables S |-| finite_pattern_variables (finite_schema_conclusion S)
    in case (liveness_unifier S p, resolution_view_pattern Vh (finite_schema_conclusion S)) of
      (Some u, Some (hi,ho)) \<Rightarrow>
        let b = liveness_binding u;
            G0 = finite_pattern_variables hi |\<union>| ffilter (\<lambda>a. finite_pattern_variables (b a) = {||})
              (finite_pattern_variables ho);
            CL = (case liveness_need D S s G0 I of None \<Rightarrow> {||} | Some R \<Rightarrow> R);
            CV = ffUnion ((\<lambda>(q,i,w). w) |`| CL);
            own = finite_socket_own Vp S s;
            call = finite_pattern_substitute (\<lambda>a. if a |\<in>| G0 then Finite_Pattern_Payload [] else b a)
              (finite_schema_conclusion S);
            open_output = (case finite_relation_option (finite_schema_premises S) s of None \<Rightarrow> True
              | Some (d,ps) \<Rightarrow> (case resolution_view_pattern Vp (finite_pattern_substitute b ps) of None \<Rightarrow> False
                | Some (xs,ys) \<Rightarrow> finite_pattern_variables ys \<noteq> {||}))
        in \<lparr>reading_matched = True, reading_ground = (liveness_need D S s G0 I \<noteq> None \<and> open_output),
          reading_closed = (\<lambda>(q,i,w). q) |`| CL,
          reading_children = (CV |\<inter>| C = {||}),
          reading_premise_only = (PO |\<inter>| CV |\<inter>| C = {||}),
          reading_outputs = (keep \<or> (case resolution_view_pattern Vh call of None \<Rightarrow> False | Some (xc,oc) \<Rightarrow>
            finite_pattern_variables xc |\<inter>| finite_pattern_variables oc = {||} \<and>
            (if \<not> after then finite_variant ho oc
            else
              fBall (finite_pattern_variables ho) (\<lambda>a. a |\<in>| C \<longrightarrow> a |\<notin>| own \<longrightarrow>
                (case b a of Finite_Variable v \<Rightarrow>
                    fBall (finite_pattern_variables ho) (\<lambda>a'. a' \<noteq> a \<longrightarrow> v |\<notin>| finite_pattern_variables (b a'))
                  | _ \<Rightarrow> False)) \<and>
              fBall (finite_pattern_variables ho) (\<lambda>a. a |\<notin>| C \<longrightarrow> fBall (finite_pattern_variables ho) (\<lambda>a'.
                a' |\<in>| C \<longrightarrow> finite_pattern_variables (b a) |\<inter>| finite_pattern_variables (b a') = {||})))))\<rparr>
    | _ \<Rightarrow> \<lparr>reading_matched = False, reading_ground = False, reading_closed = {||}, reading_children = False,
        reading_premise_only = False, reading_outputs = False\<rparr>)"

definition liveness_holds :: "liveness_reading \<Rightarrow> bool" where
  "liveness_holds r \<longleftrightarrow> reading_matched r \<and> reading_ground r \<and> reading_children r \<and> reading_premise_only r \<and>
    reading_outputs r"

text \<open>The frame choices of a socket: the default today; the default and its declared frames after.\<close>

definition liveness_choices ::
    "(nat,nat,nat) resolution_frames \<Rightarrow> bool \<Rightarrow> liveness_socket \<Rightarrow> nat fset option fset" where
  "liveness_choices \<Phi> after \<sigma> = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow>
    if after then finsert None ((\<lambda>(e',S',s',C). Some C) |`| ffilter (\<lambda>(e',S',s',C). e' = e \<and> S' = S \<and> s' = s) \<Phi>)
    else {|None|})"

section \<open>The parent committed, and the least fixpoint\<close>

text \<open>
  A direct commitment: the producer's view reads the call with an output Y, its input fed in the caller's clause, and
  every other premise of the caller's clause holding a variable of Y a declared consumer of the producer at a hole of
  its view (@{const finite_output_consumer}'s condition), no material premise holding one. Strictly (the clause
  decides) Y also stays out of the caller's head; leniently it may reach it.
\<close>

definition liveness_direct ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> liveness_caller \<Rightarrow> bool" where
  "liveness_direct D lenient e c = (case c of (f,cc,S',k,p) \<Rightarrow> fBex (declared_producers D) (\<lambda>(d,V,hs). d = e \<and>
    (case resolution_view_pattern V p of None \<Rightarrow> False
    | Some (x,y) \<Rightarrow> finite_pattern_variables y \<noteq> {||} \<and>
        liveness_need D S' k (liveness_head_inputs D f S') (finite_pattern_variables x) \<noteq> None \<and>
        (lenient \<or> finite_pattern_variables y |\<inter>| finite_pattern_variables (finite_schema_conclusion S') = {||}) \<and>
        fBall (finite_schema_premises S') (\<lambda>(k',e'',p'). k' = k \<or>
          finite_pattern_variables p' |\<inter>| finite_pattern_variables y = {||} \<or>
          fBex (declared_consumers D) (\<lambda>(d',e',V',i). d' = e \<and> e' = e'' \<and> i < length hs \<and>
            (case resolution_view_pattern V' p' of None \<Rightarrow> False
            | Some (x',z) \<Rightarrow> z = resolution_view_hole_patterns V hs p ! i \<and>
                finite_pattern_variables x' |\<inter>| finite_pattern_variables y = {||}))) \<and>
        fBall (finite_schema_materials S') (\<lambda>(k',N).
          finite_material_variables N |\<inter>| finite_pattern_variables y = {||}))))"

section \<open>Names\<close>

text \<open>
  A socket is named by its site, its clause's key in the asked program and its key; a caller premise likewise, so that
  a caller premise is a live socket exactly when their names agree; a clause not in the program by 999.
\<close>

type_synonym liveness_label = "nat \<times> nat \<times> nat"

definition liveness_clause_key ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) finite_factor_schema \<Rightarrow> nat" where
  "liveness_clause_key P e S =
    fMin (finsert 999 ((\<lambda>((d,cc),S'). cc) |`| ffilter (\<lambda>((d,cc),S'). d = e \<and> S' = S) (finite_system_clauses P)))"

definition liveness_name :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> liveness_socket \<Rightarrow> liveness_label" where
  "liveness_name P \<sigma> = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow> (e,liveness_clause_key P e S,s))"

definition liveness_caller_name :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> liveness_caller \<Rightarrow> liveness_label" where
  "liveness_caller_name P c = (case c of (f,cc,S',k,p) \<Rightarrow> (f,liveness_clause_key P f S',k))"

text \<open>The goals a socket commits when it is live: its premise's callee; none at a material premise.\<close>

definition liveness_goals :: "liveness_socket \<Rightarrow> nat fset" where
  "liveness_goals \<sigma> = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow>
    (\<lambda>(k,d,p). d) |`| ffilter (\<lambda>(k,d,p). k = s) (finite_schema_premises S))"

section \<open>The readings of a direct commitment, and the joint least fixpoint\<close>

text \<open>
  The clause-level readings are computed once into tables: the direct commitments of a producer at its route callers,
  strict and lenient; the route callers at which a socket's test holds at some frame choice; each socket's keep flag
  and goals. The readings of a lenient direct commitment are named values.
\<close>

datatype commitment_reading = Strict_Reading | Focused_Reading | Lenient_Reading

type_synonym liveness_tables = "(nat \<times> liveness_label) fset \<times> (nat \<times> liveness_label) fset \<times>
  (liveness_label \<times> liveness_label) fset \<times> (liveness_label \<times> bool \<times> nat fset) fset"

definition liveness_tables ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> nat fset \<Rightarrow> bool \<Rightarrow> liveness_tables" where
  "liveness_tables P D \<Phi> R after = (let
      callers = liveness_route_callers P R;
      sites = (\<lambda>(d,V,hs). d) |`| declared_producers D;
      direct = (\<lambda>lenient. ffUnion ((\<lambda>e. (\<lambda>c. (e,liveness_caller_name P c)) |`|
        ffilter (liveness_direct D lenient e) (callers e)) |`| sites));
      tested = ffUnion ((\<lambda>\<sigma>. (\<lambda>c. (liveness_name P \<sigma>,liveness_caller_name P c)) |`| ffilter (\<lambda>c. case \<sigma> of
          (e,S,s,keep,Vp,Vh) \<Rightarrow> fBex (finite_system_clauses P) (\<lambda>((d,cc),S'). d = e \<and> S' = S) \<and>
            fBex (liveness_choices \<Phi> after \<sigma>) (\<lambda>ch. liveness_holds (liveness_read D \<sigma> after ch c)))
        (callers (fst \<sigma>))) |`| declared_sockets D);
      rows = (\<lambda>\<sigma>. (liveness_name P \<sigma>,case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow> keep,liveness_goals \<sigma>)) |`| declared_sockets D
    in (direct False,direct True,tested,rows))"

text \<open>
  The parent at a caller is committed directly (strictly always; a lenient direct commitment in the focused reading
  where the caller's site is committed, and always in the lenient one), or at the caller's premise when that premise
  is a live socket. A site is committed where it is committed at some route caller or is the goal of a live socket.
\<close>

definition liveness_committed ::
    "commitment_reading \<Rightarrow> liveness_tables \<Rightarrow> nat fset \<Rightarrow> liveness_label fset \<Rightarrow> nat \<Rightarrow> liveness_label \<Rightarrow> bool" where
  "liveness_committed r T K L e n = (case T of (DS,DL,RT,KG) \<Rightarrow> (e,n) |\<in>| DS \<or>
    ((e,n) |\<in>| DL \<and> (r = Lenient_Reading \<or> (r = Focused_Reading \<and> fst n |\<in>| K))) \<or> n |\<in>| L)"

definition liveness_step ::
    "commitment_reading \<Rightarrow> liveness_tables \<Rightarrow> nat fset \<times> liveness_label fset \<Rightarrow> nat fset \<times> liveness_label fset" where
  "liveness_step r T KL = (case (T,KL) of ((DS,DL,RT,KG),(K,L)) \<Rightarrow>
    (fst |`| ffilter (\<lambda>(e,n). liveness_committed r T K L e n) (DS |\<union>| DL) |\<union>|
       ffUnion ((\<lambda>(m,keep,G). G) |`| ffilter (\<lambda>(m,keep,G). m |\<in>| L) KG),
     (\<lambda>(m,keep,G). m) |`| ffilter (\<lambda>(m,keep,G). fBex RT (\<lambda>(m',n). m' = m \<and>
       (keep \<or> liveness_committed r T K L (fst m) n))) KG))"

text \<open>The step is monotone and its values bounded, so the iteration from nothing reaches its least fixpoint.\<close>

definition liveness_fixpoint :: "commitment_reading \<Rightarrow> liveness_tables \<Rightarrow> nat fset \<times> liveness_label fset" where
  "liveness_fixpoint r T = (case T of (DS,DL,RT,KG) \<Rightarrow>
    (liveness_step r T ^^ Suc (fcard (DS |\<union>| DL) + 2 * fcard KG)) ({||},{||}))"

section \<open>The three tests\<close>

text \<open>
  Today correction (9)'s test (the default frame and the variant test); after at no frames the framed test with no
  frame declared ((iii) at the default frame); after the framed test at the declared frames.
\<close>

datatype liveness_test = Today_Test | Unframed_Test | Framed_Test

definition liveness_test_tables ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat fset \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> liveness_test \<Rightarrow> liveness_tables" where
  "liveness_test_tables P R D \<Phi> t = liveness_tables P D (if t = Framed_Test then \<Phi> else {||}) R (t \<noteq> Today_Test)"

text \<open>
  The evaluation over a program and the sites whose clauses count as callers: the asked program and the route for the
  guard; the whole of a program to read a socket off the route as it stands.
\<close>

definition liveness_evaluation ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat fset \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow>
      (liveness_test \<times> (commitment_reading \<times> liveness_label fset) list) list \<times> liveness_label fset \<times>
      liveness_label fset" where
  "liveness_evaluation P R D \<Phi> = (let
      rows = map (\<lambda>t. let T = liveness_test_tables P R D \<Phi> t in
        (t,map (\<lambda>r. (r,snd (liveness_fixpoint r T))) [Strict_Reading,Focused_Reading,Lenient_Reading]))
        [Today_Test,Unframed_Test,Framed_Test];
      names = liveness_name P |`| declared_sockets D;
      off = liveness_name P |`| ffilter (\<lambda>\<sigma>. liveness_route_callers P R (fst \<sigma>) = {||}) (declared_sockets D);
      live = ffUnion (fset_of_list (concat (map (\<lambda>(t,xs). map snd xs) rows)))
    in (rows,off,names |-| off |-| live))"

text \<open>
  The reading at every route caller of every socket, its parent committed or not and each frame choice's reading, for
  the inspection of a disagreement; this theory states only the names below.
\<close>

definition liveness_detail where
  "liveness_detail P R D \<Phi> t r = (let after = (t \<noteq> Today_Test);
      \<Phi>' = (if t = Framed_Test then \<Phi> else {||}); T = liveness_test_tables P R D \<Phi> t; KL = liveness_fixpoint r T in
    (\<lambda>\<sigma>. (liveness_name P \<sigma>, (\<lambda>c. (liveness_caller_name P c,
        (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow> keep \<or> liveness_committed r T (fst KL) (snd KL) e (liveness_caller_name P c)),
        (\<lambda>ch. (ch, liveness_read D \<sigma> after ch c)) |`| liveness_choices \<Phi>' after \<sigma>)) |`|
      liveness_route_callers P R (fst \<sigma>))) |`| declared_sockets D)"

text \<open>The declarations with only the sockets at one site, and the callers at which a producer is committed directly.\<close>

definition liveness_sockets_at ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) resolution_declarations" where
  "liveness_sockets_at D e = \<lparr>declared_producers = declared_producers D, declared_consumers = declared_consumers D,
    declared_sockets = ffilter (\<lambda>\<sigma>. fst \<sigma> = e) (declared_sockets D)\<rparr>"

definition liveness_direct_callers ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat fset \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow> bool \<Rightarrow>
      nat \<Rightarrow> liveness_label fset" where
  "liveness_direct_callers P R D lenient e =
    liveness_caller_name P |`| ffilter (liveness_direct D lenient e) (liveness_route_callers P R e)"

section \<open>The declared sockets on the guard's route, today and after, in the three readings\<close>

text \<open>
  One evaluation over the asked program, compiled once, with every landed record and frame: R6's, #601's, #603's,
  #607's, #679's, #758's and #760's, #609's narrowed sockets read as their sockets, and #681's (its consumers at 72
  and 503, its kept socket 105.0/2 and its free socket at 587, whose clause is no clause of the asked program and is
  named by 999). For each test the live sockets strictly, focused and leniently; then the sockets off the route, and
  those on it live in no reading of any test. #681's records change no name on the route: its two sockets are off
  it, and its consumers decide no direct commitment at a route caller.
\<close>

text \<open>
  Then #681's three points as they stand (plan-105, from review 682's follow-up 2), nothing declared to change them.
  (a) 65's route callers are 69.0/0, 73.0/0, 82.0/1 and 503.0/0, and 65 is committed directly at none, strictly or
  leniently: its table is premise-only there, so the consumers 500–502 declared at 503.0/0 are never read on the
  route. (b) 105.0/2 and 105.1/2, off the route, read over the whole asked program: live after at their declared
  frames in every reading, dead today and at no frames. (c) 587.0/0 in the stated-leaves program: at its one caller
  588.0/0 the socket's test holds today and after (the variant test at @{const stated_view} with the literal payloads
  of 587's head output, and (iii) at the default frame and at {4,7}), but 587 is committed directly at no caller, so
  the free socket is dead in every reading.
\<close>

lemma socket_liveness:
  "liveness_evaluation finite_asked_program liveness_route liveness_declarations liveness_frames =
    ([(Today_Test,
        [(Strict_Reading, {|(32,0,0),(40,0,0),(79,0,1),(83,0,1)|}),
         (Focused_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(32,0,0),(40,0,0),(79,0,1),
            (83,0,1)|}),
         (Lenient_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(32,0,0),(40,0,0),(79,0,1),
            (83,0,1)|})]),
      (Unframed_Test,
        [(Strict_Reading, {|(32,0,0),(40,0,0),(79,0,1),(83,0,1)|}),
         (Focused_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(32,0,0),(40,0,0),(79,0,1),
            (83,0,1)|}),
         (Lenient_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(32,0,0),(40,0,0),(62,0,0),
            (63,1,0),(63,1,1),(63,2,0),(63,2,1),(79,0,1),(83,0,1)|})]),
      (Framed_Test,
        [(Strict_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(12,0,2),(29,0,5),(32,0,0),(37,0,2),(40,0,0),
            (75,0,3),(79,0,1),(81,0,3),(83,0,1),(505,0,4)|}),
         (Focused_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(29,0,5),(32,0,0),(37,0,2),
            (40,0,0),(75,0,3),(79,0,1),(81,0,3),(83,0,1),(505,0,4)|}),
         (Lenient_Reading, {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(29,0,5),(29,0,7),(32,0,0),
            (37,0,2),(40,0,0),(50,2,2),(50,2,3),(50,2,7),(55,1,1),(55,2,2),(55,2,3),(55,2,7),(55,2,8),(57,0,4),
            (57,0,8),(60,1,0),(60,1,1),(60,1,4),(60,1,5),(61,0,4),(62,0,0),(63,1,0),(63,1,1),(63,1,2),(63,2,0),
            (63,2,1),(63,2,2),(75,0,3),(79,0,1),(81,0,3),(83,0,1),(505,0,4)|})])],
     {|(58,0,0),(104,1,3),(105,0,2),(105,1,2),(119,0,1),(587,999,0)|},
     {|(29,0,6),(36,3,5),(45,1,2),(54,0,1),(64,0,1),(64,0,2),(65,0,3),(65,0,4),(71,0,1)|}) \<and>
   liveness_caller_name finite_asked_program |`| liveness_route_callers finite_asked_program liveness_route 65 =
     {|(69,0,0),(73,0,0),(82,0,1),(503,0,0)|} \<and>
   liveness_direct_callers finite_asked_program liveness_route liveness_declarations False 65 = {||} \<and>
   liveness_direct_callers finite_asked_program liveness_route liveness_declarations True 65 = {||} \<and>
   liveness_evaluation finite_asked_program (finite_system_definitions finite_asked_program)
      (liveness_sockets_at liveness_declarations 105) liveness_frames =
    ([(Today_Test, [(Strict_Reading, {||}), (Focused_Reading, {||}), (Lenient_Reading, {||})]),
      (Unframed_Test, [(Strict_Reading, {||}), (Focused_Reading, {||}), (Lenient_Reading, {||})]),
      (Framed_Test, [(Strict_Reading, {|(105,0,2),(105,1,2)|}), (Focused_Reading, {|(105,0,2),(105,1,2)|}),
        (Lenient_Reading, {|(105,0,2),(105,1,2)|})])], {||}, {||}) \<and>
   liveness_evaluation finite_stated_report_program (finite_system_definitions finite_stated_report_program)
      (liveness_sockets_at liveness_declarations 587) liveness_frames =
    ([(Today_Test, [(Strict_Reading, {||}), (Focused_Reading, {||}), (Lenient_Reading, {||})]),
      (Unframed_Test, [(Strict_Reading, {||}), (Focused_Reading, {||}), (Lenient_Reading, {||})]),
      (Framed_Test, [(Strict_Reading, {||}), (Focused_Reading, {||}), (Lenient_Reading, {||})])],
     {||}, {|(587,0,0)|}) \<and>
   liveness_direct_callers finite_stated_report_program (finite_system_definitions finite_stated_report_program)
      liveness_declarations True 587 = {||} \<and>
   liveness_detail finite_stated_report_program (finite_system_definitions finite_stated_report_program)
      (liveness_sockets_at liveness_declarations 587) liveness_frames Framed_Test Focused_Reading =
    {|((587,0,0), {|((588,0,0), False, {|
      (None, \<lparr>reading_matched = True, reading_ground = True, reading_closed = {||}, reading_children = True,
        reading_premise_only = True, reading_outputs = True\<rparr>),
      (Some {|4,7|}, \<lparr>reading_matched = True, reading_ground = True, reading_closed = {||},
        reading_children = True, reading_premise_only = True, reading_outputs = True\<rparr>)|})|})|} \<and>
   liveness_detail finite_stated_report_program (finite_system_definitions finite_stated_report_program)
      (liveness_sockets_at liveness_declarations 587) liveness_frames Today_Test Focused_Reading =
    {|((587,0,0), {|((588,0,0), False, {|
      (None, \<lparr>reading_matched = True, reading_ground = True, reading_closed = {||}, reading_children = True,
        reading_premise_only = True, reading_outputs = True\<rparr>)|})|})|}"
  by eval

end
