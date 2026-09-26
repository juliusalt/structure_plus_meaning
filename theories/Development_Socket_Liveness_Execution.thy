theory Development_Socket_Liveness_Execution
  imports Development_First_Problem_Asked Development_Given_Carried_Declarations
    Factor_Schema_Instantiation_Declarations Native_Execution_Refinements
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
  a declared socket live there: a least fixpoint over the sockets. Where the output's variables reach the caller's
  head, goals outside the clause may hold them and the clause does not decide the consumers: such commitments are
  counted only in the lenient reading, and the sockets live only under it are named apart. A kept socket needs no
  committed parent. What the evaluation cannot read it does not guess: the order the search takes goals, and a
  caller variable ground by the caller's own earlier premises beyond what its clause shows.
\<close>

text \<open>
  The records' clauses are written with @{const finite_pattern_of}, whose target case reads an artifact's finite
  presentation by a description; no socket clause holds a target, so that case aborts here and is never reached.
\<close>

declare [[code abort: finite_object_of]]

definition liveness_declarations :: "(nat,nat,nat) resolution_declarations" where
  "liveness_declarations = declarations_list [given_declarations, quotation_declarations, binding_declarations,
    instantiation_declarations, scoped_declarations, prospective_declarations, application_declarations,
    row_values_declarations, vector_declarations, record_declarations, material_declarations,
    premise_rows_declarations, premise_family_declarations, schema_declarations]"

definition liveness_frames :: "(nat,nat,nat) resolution_frames" where
  "liveness_frames = lookup_frames |\<union>| identity_frames |\<union>| comparison_frames |\<union>| headed_frames |\<union>|
    family_rows_frames |\<union>| admission_frames |\<union>| interpretation_frames |\<union>| binder_frames |\<union>| quotation_frames |\<union>|
    instantiation_frames |\<union>| prospective_frames |\<union>| application_frames |\<union>| vector_frames |\<union>| record_frames |\<union>|
    material_frames |\<union>| premise_rows_frames |\<union>| premise_family_frames |\<union>| schema_frames"

type_synonym liveness_socket =
  "nat \<times> (nat,nat,nat) finite_factor_schema \<times> nat \<times> bool \<times> nat resolution_view \<times> nat resolution_view"

type_synonym liveness_caller = "nat \<times> nat \<times> (nat,nat,nat) finite_factor_schema \<times> nat \<times> nat finite_term_pattern"

section \<open>The callers and the parent's bindings\<close>

definition liveness_callers ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> nat \<Rightarrow> liveness_caller fset" where
  "liveness_callers P e = ffUnion ((\<lambda>((f,c),S'). (\<lambda>(k,d,p). (f,c,S',k,p)) |`|
      ffilter (\<lambda>(k,d,p). d = e) (finite_schema_premises S')) |`| finite_system_clauses P)"

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

definition liveness_committed ::
    "(nat,nat,nat) resolution_declarations \<Rightarrow> bool \<Rightarrow> liveness_socket fset \<Rightarrow> nat \<Rightarrow> liveness_caller \<Rightarrow> bool" where
  "liveness_committed D lenient L e c = (case c of (f,cc,S',k,p) \<Rightarrow>
    liveness_direct D lenient e c \<or> fBex L (\<lambda>(e',S'',s',keep',Vp',Vh'). e' = f \<and> S'' = S' \<and> s' = k))"

definition liveness_live_at ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> liveness_socket fset \<Rightarrow> liveness_socket \<Rightarrow>
      liveness_caller \<Rightarrow> bool" where
  "liveness_live_at P D \<Phi> after lenient L \<sigma> c = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow>
    fBex (finite_system_clauses P) (\<lambda>((d,cc),S'). d = e \<and> S' = S) \<and>
    (keep \<or> liveness_committed D lenient L e c) \<and>
    fBex (liveness_choices \<Phi> after \<sigma>) (\<lambda>ch. liveness_holds (liveness_read D \<sigma> after ch c)))"

definition liveness_step ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> liveness_socket fset \<Rightarrow> liveness_socket fset" where
  "liveness_step P D \<Phi> after lenient L = ffilter (\<lambda>\<sigma>. fBex (liveness_callers P (fst \<sigma>))
    (liveness_live_at P D \<Phi> after lenient L \<sigma>)) (declared_sockets D)"

definition liveness_live ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> (nat,nat,nat) resolution_declarations \<Rightarrow>
      (nat,nat,nat) resolution_frames \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> liveness_socket fset" where
  "liveness_live P D \<Phi> after lenient = (liveness_step P D \<Phi> after lenient ^^ Suc (fcard (declared_sockets D))) {||}"

section \<open>Names\<close>

text \<open>A socket is named by its site, its clause's key in the asked program and its key; a clause not in it by 999.\<close>

definition liveness_name ::
    "(nat,nat,nat,nat) finite_schema_system \<Rightarrow> liveness_socket \<Rightarrow> nat \<times> nat \<times> nat" where
  "liveness_name P \<sigma> = (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow>
    (e,fMin (finsert 999 ((\<lambda>((d,cc),S'). cc) |`| ffilter (\<lambda>((d,cc),S'). d = e \<and> S' = S) (finite_system_clauses P))),s))"

definition liveness_names :: "liveness_socket fset \<Rightarrow> (nat \<times> nat \<times> nat) fset" where
  "liveness_names L = liveness_name finite_asked_program |`| L"

text \<open>
  The reading at every caller of every socket, its parent committed or not and each frame choice's reading, for the
  inspection of a disagreement; this theory states only the names below.
\<close>

definition liveness_detail where
  "liveness_detail after lenient = (let P = finite_asked_program; D = liveness_declarations; \<Phi> = liveness_frames;
      L = liveness_live P D \<Phi> after lenient in
    (\<lambda>\<sigma>. (liveness_name P \<sigma>, (\<lambda>c. case c of (f,cc,S',k,p) \<Rightarrow> ((f,cc,k),
        (case \<sigma> of (e,S,s,keep,Vp,Vh) \<Rightarrow> keep \<or> liveness_committed D lenient L e c),
        (\<lambda>ch. (ch, liveness_read D \<sigma> after ch c)) |`| liveness_choices \<Phi> after \<sigma>)) |`| liveness_callers P (fst \<sigma>)))
      |`| declared_sockets D)"

section \<open>The declared sockets live and dead, today and after\<close>

text \<open>
  One evaluation over the asked program, compiled once: the 37 sockets the records declare (R6's, #601's, #603's,
  #607's and #679's), by name. Strictly (every direct commitment decided by its clause) live and dead under today's
  test and after; then the sockets live only in the lenient reading, where a direct commitment's output reaches the
  caller's head and goals outside the clause may hold it. Every socket's clause is a clause of the asked program (no
  name holds 999).
\<close>

lemma socket_liveness:
  "liveness_names (liveness_live finite_asked_program liveness_declarations liveness_frames False False) =
      {|(32,0,0),(40,0,0),(54,0,1),(79,0,1),(83,0,1)|} \<and>
   liveness_names (declared_sockets liveness_declarations |-|
      liveness_live finite_asked_program liveness_declarations liveness_frames False False) =
      {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(29,0,5),(29,0,6),(29,0,7),(36,3,5),(37,0,2),
        (45,1,2),(50,2,2),(50,2,3),(55,1,1),(55,2,2),(55,2,3),(57,0,4),(58,0,0),(60,1,0),(60,1,1),(61,0,4),
        (62,0,0),(63,1,0),(63,1,1),(63,2,0),(63,2,1),(64,0,1),(64,0,2),(65,0,3),(65,0,4)|} \<and>
   liveness_names (liveness_live finite_asked_program liveness_declarations liveness_frames True False) =
      {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(12,0,2),(29,0,5),(32,0,0),(37,0,2),(40,0,0),(54,0,1),
        (79,0,1),(83,0,1)|} \<and>
   liveness_names (declared_sockets liveness_declarations |-|
      liveness_live finite_asked_program liveness_declarations liveness_frames True False) =
      {|(10,0,4),(29,0,6),(29,0,7),(36,3,5),(45,1,2),(50,2,2),(50,2,3),(55,1,1),(55,2,2),(55,2,3),(57,0,4),
        (58,0,0),(60,1,0),(60,1,1),(61,0,4),(62,0,0),(63,1,0),(63,1,1),(63,2,0),(63,2,1),(64,0,1),(64,0,2),
        (65,0,3),(65,0,4)|} \<and>
   liveness_names (liveness_live finite_asked_program liveness_declarations liveness_frames False True |-|
      liveness_live finite_asked_program liveness_declarations liveness_frames False False) =
      {|(6,1,1),(7,0,0),(7,0,1),(7,0,2),(7,0,3),(10,0,4),(12,0,2),(58,0,0)|} \<and>
   liveness_names (liveness_live finite_asked_program liveness_declarations liveness_frames True True |-|
      liveness_live finite_asked_program liveness_declarations liveness_frames True False) =
      {|(10,0,4),(29,0,7),(50,2,2),(50,2,3),(55,1,1),(55,2,2),(55,2,3),(57,0,4),(58,0,0),(60,1,0),(60,1,1),
        (61,0,4),(62,0,0),(63,1,0),(63,1,1),(63,2,0),(63,2,1)|}"
  by eval

end
