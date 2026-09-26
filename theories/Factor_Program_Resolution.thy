theory Factor_Program_Resolution
  imports Factor_Material_Resolution Factor_Pattern_Unification Factor_Finite_Proof_Checking
    Factor_Finite_Schema_Renaming
begin

section \<open>Goals, derivation nodes and states\<close>

text \<open>
  A clause resolving a goal at a derivation position is renamed apart at that position: its variables
  are paired with the position and @{const True}, the interface's with the position and @{const False}
  (@{const finite_rename_apart}). A goal is a call pattern at a site, or a material premise, each at its
  position and naming the clause and socket that raised it. A node records the clause that resolved a
  goal, the call it resolved and the current instance of each of the clause's own variables.
\<close>

type_synonym ('s,'a) resolution_variable = "('s list \<times> bool) \<times> 'a"

datatype ('a,'s,'d,'c) resolution_goal =
    Resolution_Call_Goal "'s list" "('d \<times> 'c \<times> 's) option" 'd "('s,'a) resolution_variable finite_term_pattern"
  | Resolution_Material_Goal "'s list" "'d \<times> 'c \<times> 's" "('s,'a) resolution_variable finite_material_pattern"

fun resolution_goal_position :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> 's list" where
  "resolution_goal_position (Resolution_Call_Goal q r d p) = q"
| "resolution_goal_position (Resolution_Material_Goal q r M) = q"

fun resolution_goal_variables :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> ('s,'a) resolution_variable fset" where
  "resolution_goal_variables (Resolution_Call_Goal q r d p) = finite_pattern_variables p"
| "resolution_goal_variables (Resolution_Material_Goal q r M) = finite_material_variables M"

definition finite_material_pattern_substitute ::
    "('v \<Rightarrow> 'w finite_term_pattern) \<Rightarrow> 'v finite_material_pattern \<Rightarrow> 'w finite_material_pattern" where
  "finite_material_pattern_substitute \<sigma> M =
    \<lparr>finite_material_source=finite_pattern_substitute \<sigma> (finite_material_source M),
     finite_material_atoms=finite_pattern_substitute \<sigma> (finite_material_atoms M),
     finite_material_edges=finite_pattern_substitute \<sigma> (finite_material_edges M),
     finite_material_counts=finite_pattern_substitute \<sigma> (finite_material_counts M),
     finite_material_functions=finite_pattern_substitute \<sigma> (finite_material_functions M)\<rparr>"

fun resolution_goal_substitute ::
    "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_goal" where
  "resolution_goal_substitute \<sigma> (Resolution_Call_Goal q r d p) =
    Resolution_Call_Goal q r d (finite_pattern_substitute \<sigma> p)"
| "resolution_goal_substitute \<sigma> (Resolution_Material_Goal q r M) =
    Resolution_Material_Goal q r (finite_material_pattern_substitute \<sigma> M)"

datatype ('a,'s,'d,'c) resolution_node = Resolution_Node
  (resolution_node_position: "'s list") (resolution_node_site: 'd) (resolution_node_clause: 'c)
  (resolution_node_schema: "('a,'s,'d) finite_factor_schema")
  (resolution_node_call: "('s,'a) resolution_variable finite_term_pattern")
  (resolution_node_bindings: "('a \<times> ('s,'a) resolution_variable finite_term_pattern) fset")

fun resolution_node_substitute ::
    "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) resolution_node" where
  "resolution_node_substitute \<sigma> (Resolution_Node q d c S p B) =
    Resolution_Node q d c S (finite_pattern_substitute \<sigma> p) (fimage (\<lambda>(a,x). (a,finite_pattern_substitute \<sigma> x)) B)"

text \<open>
  A state holds the pending goals, the nodes of the derivation so far, and the values the witness
  construction supplied on its branch.
\<close>

datatype ('a,'s,'d,'c) resolution_state = Resolution_State
  (resolution_pending: "('a,'s,'d,'c) resolution_goal fset")
  (resolution_nodes: "('a,'s,'d,'c) resolution_node fset")
  (resolution_witnesses: "(('s,'a) resolution_variable \<times> finite_factor_term) fset")

definition resolution_state_substitute ::
    "(('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern) \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "resolution_state_substitute \<sigma> st = Resolution_State (fimage (resolution_goal_substitute \<sigma>) (resolution_pending st))
    (fimage (resolution_node_substitute \<sigma>) (resolution_nodes st)) (resolution_witnesses st)"

section \<open>The step\<close>

text \<open>
  A call goal is resolved by a clause of its site: the site's interface and the clause's head, both
  renamed apart at the goal's position, are unified with the goal by R2's most general unifier; the
  clause's premises become goals at their sockets and its material premises material goals, and the
  unifier is applied to the whole state. Every clause and every interface of the site is an
  alternative; the alternatives form a finite set, so no clause key and no listing order chooses
  among them.
\<close>

definition finite_clause_goals ::
    "'s list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_clause_goals q d c S =
    fimage (\<lambda>(s,e,p). Resolution_Call_Goal (q@[s]) (Some (d,c,s)) e (finite_rename_apart (q,True) p))
      (finite_schema_premises S) |\<union>|
    fimage (\<lambda>(s,M). Resolution_Material_Goal (q@[s]) (d,c,s) (finite_rename_material (Pair (q,True)) M))
      (finite_schema_materials S)"

definition finite_clause_node ::
    "'s list \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> ('a,'s,'d,'c) resolution_node" where
  "finite_clause_node q d c S = Resolution_Node q d c S (finite_rename_apart (q,True) (finite_schema_conclusion S))
    (fimage (\<lambda>a. (a,Finite_Variable ((q,True),a))) (finite_schema_variables S))"

definition finite_call_successors ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow>
      ('d \<times> 'c \<times> 's) option \<Rightarrow> 'd \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern \<Rightarrow>
      ('a,'s,'d,'c) resolution_state fset" where
  "finite_call_successors P st q r d p = ffUnion (fimage (\<lambda>(e,i). if e\<noteq>d then {||} else
      ffUnion (fimage (\<lambda>((e',c),S). if e'\<noteq>d then {||} else
        (case finite_unify_pairs [(finite_rename_apart (q,False) i,p),
            (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] of
          None \<Rightarrow> {||}
        | Some u \<Rightarrow> {|resolution_state_substitute (finite_binding_substitution u)
            (Resolution_State (finite_clause_goals q d c S |\<union>|
                (resolution_pending st |-| {|Resolution_Call_Goal q r d p|}))
              (finsert (finite_clause_node q d c S) (resolution_nodes st)) (resolution_witnesses st))|}))
        (finite_system_clauses P)))
    (finite_system_interfaces P))"

text \<open>
  A material goal is solved by R1's resolution: each solution W of @{const finite_material_resolution}
  gives one successor, the goal removed and each field bound to its instance under W, by unifying the
  field with the exact pattern of that instance. A solution binds exactly the goal's variables,
  functionally (@{thm [source] finite_material_resolution_exact}), so each field has one instance and
  the unifier binds each variable of the goal to its value in W. A material goal R1 leaves waiting is
  not selected.
\<close>

definition finite_material_instance_pairs ::
    "('v \<times> finite_factor_term) fset \<Rightarrow> 'v finite_material_pattern \<Rightarrow> 'v finite_pattern_pairs fset" where
  "finite_material_instance_pairs W M =
    ffUnion (fimage (\<lambda>s. ffUnion (fimage (\<lambda>a. ffUnion (fimage (\<lambda>e. ffUnion (fimage (\<lambda>b. fimage (\<lambda>f.
      [(finite_material_source M,finite_exact_term_pattern s),(finite_material_atoms M,finite_exact_term_pattern a),
       (finite_material_edges M,finite_exact_term_pattern e),(finite_material_counts M,finite_exact_term_pattern b),
       (finite_material_functions M,finite_exact_term_pattern f)])
      (finite_pattern_instances W (finite_material_functions M)))
      (finite_pattern_instances W (finite_material_counts M))))
      (finite_pattern_instances W (finite_material_edges M))))
      (finite_pattern_instances W (finite_material_atoms M))))
      (finite_pattern_instances W (finite_material_source M)))"

definition finite_material_successors ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> 's list \<Rightarrow> 'd \<times> 'c \<times> 's \<Rightarrow>
      ('s,'a) resolution_variable finite_material_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_material_successors st q r M = (case finite_material_resolution M of
      Material_Waits \<Rightarrow> {||}
    | Material_Solutions Ws \<Rightarrow> ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E.
        case finite_unify_pairs E of
          None \<Rightarrow> {||}
        | Some u \<Rightarrow> {|resolution_state_substitute (finite_binding_substitution u)
            (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|})
              (resolution_nodes st) (resolution_witnesses st))|})
      (finite_material_instance_pairs W M))) Ws))"

text \<open>
  A node is solved when no pending goal stands at or under its position (F3 of the addition "The resolver at the
  given's size" to task 495's entry). A position stands left of another when the first socket at which they differ is
  less in it, so neither is a prefix of the other. A ground call goal equal, in site and pattern, to the call of a solved
  node standing left of it is closed by that node's derivation: its one successor removes the goal and substitutes
  nothing, and no clause alternative is kept beside it. The target stands left of the goal, so a certificate's reuse
  follows the order of positions and never returns to the node whose premise it closes; the waiting rule of the
  selection solves the leftmost occurrence first.
\<close>

definition finite_solved_node :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> bool" where
  "finite_solved_node st nd \<longleftrightarrow> \<not> fBex (resolution_pending st) (\<lambda>g.
    take (length (resolution_node_position nd)) (resolution_goal_position g) = resolution_node_position nd)"

fun finite_position_left :: "'s::linorder list \<Rightarrow> 's list \<Rightarrow> bool" where
  "finite_position_left (x#xs) (y#ys) = (x<y \<or> x=y \<and> finite_position_left xs ys)"
| "finite_position_left xs ys = False"

definition finite_reusable :: "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_reusable st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> finite_pattern_variables p={||} \<and> fBex (resolution_nodes st) (\<lambda>nd.
        finite_position_left (resolution_node_position nd) q \<and> finite_solved_node st nd \<and>
        resolution_node_site nd=d \<and> resolution_node_call nd=p)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

definition finite_goal_closed ::
    "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_goal_closed st g = Resolution_State (resolution_pending st |-| {|g|}) (resolution_nodes st) (resolution_witnesses st)"

fun finite_goal_successors ::
    "('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_state fset" where
  "finite_goal_successors P st (Resolution_Call_Goal q r d p) = (if finite_reusable st (Resolution_Call_Goal q r d p)
    then {|finite_goal_closed st (Resolution_Call_Goal q r d p)|} else finite_call_successors P st q r d p)"
| "finite_goal_successors P st (Resolution_Material_Goal q r M) = finite_material_successors st q r M"

lemma finite_reusable_successors:
  "finite_reusable st g \<Longrightarrow> finite_goal_successors P st g = {|finite_goal_closed st g|}"
  by (cases g) (simp_all add: finite_reusable_def)

lemma finite_goal_successors_unreused:
  "\<not> finite_reusable st g \<Longrightarrow> finite_goal_successors P st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> finite_call_successors P st q r d p
    | Resolution_Material_Goal q r M \<Rightarrow> finite_material_successors st q r M)"
  by (cases g) simp_all

subsection \<open>The order of positions\<close>

text \<open>
  Left of is irreflexive and transitive; a position left of a socket under q is left of q or under it; a position
  under one left of another is left of it; neither of two positions one left of the other prefixes the other. The
  order of positions is a strict total order, prefixes first.
\<close>

lemma finite_position_left_irrefl: "\<not> finite_position_left p p"
  by (induction p) auto

lemma finite_position_left_trans:
  "finite_position_left p q \<Longrightarrow> finite_position_left q r \<Longrightarrow> finite_position_left p r"
proof (induction p arbitrary: q r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain y ys where q: "q=y#ys" using Cons.prems(1) by (cases q) auto
  obtain z zs where r: "r=z#zs" using Cons.prems(2) q by (cases r) auto
  show ?case using Cons.prems Cons.IH[of ys zs] unfolding q r by auto
qed

lemma finite_position_left_socket:
  "finite_position_left p (q@[s]) \<Longrightarrow> finite_position_left p q \<or> take (length q) p = q"
proof (induction q arbitrary: p)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  obtain x xs where p: "p=x#xs" using Cons.prems by (cases p) auto
  show ?case using Cons.prems Cons.IH[of xs] unfolding p by auto
qed

lemma finite_position_left_under:
  "take (length t) x = t \<Longrightarrow> finite_position_left t z \<Longrightarrow> finite_position_left x z"
proof (induction t arbitrary: x z)
  case Nil
  then show ?case by simp
next
  case (Cons a t)
  obtain b x' where x: "x=b#x'" using Cons.prems(1) by (cases x) auto
  obtain c z' where z: "z=c#z'" using Cons.prems(2) by (cases z) auto
  show ?case using Cons.prems Cons.IH[of x' z'] unfolding x z by auto
qed

lemma finite_position_left_not_prefix:
  "finite_position_left p q \<Longrightarrow> take (length p) q \<noteq> p"
  "finite_position_left p q \<Longrightarrow> take (length q) p \<noteq> q"
proof (induction p arbitrary: q)
  case Nil
  { case 1 then show ?case by simp }
  { case 2 then show ?case by simp }
next
  case (Cons x xs)
  { case 1
    then obtain y ys where q: "q=y#ys" by (cases q) auto
    show ?case using 1 Cons.IH(1)[of ys] unfolding q by auto }
  { case 2
    then obtain y ys where q: "q=y#ys" by (cases q) auto
    show ?case using 2 Cons.IH(2)[of ys] unfolding q by auto }
qed

section \<open>The alternatives of a goal\<close>

text \<open>
  A goal's alternatives are read from R2's unifier alone, the state not substituted (F1 of the addition "The resolver at
  the given's size" to task 495's entry): at a call goal the interface-and-clause pairs of its site whose interface and
  head, renamed apart at its position, unify with its pattern; at a material goal the instance pairs of R1's solutions
  that unify. A goal's successors are the image of its alternatives, so it has none exactly when it has no alternative
  and one when it has one alternative. The count is a function of the program and the goal alone.
\<close>

text \<open>
  An alternative of a call goal is the interface, the clause key and schema of a unifying pair with its unifier; of a
  material goal, a unifying instance pair with its unifier. The unifier is determined by the pair, so the count is
  the number of unifying pairs.
\<close>

definition finite_call_alternative_set where
  "finite_call_alternative_set P q d p = ffUnion (fimage (\<lambda>(e,i). if e\<noteq>d then {||} else
      ffUnion (fimage (\<lambda>((e',c),S). if e'\<noteq>d then {||} else
        (case finite_unify_pairs [(finite_rename_apart (q,False) i,p),
            (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] of
          None \<Rightarrow> {||}
        | Some u \<Rightarrow> {|(i,c,S,u)|}))
        (finite_system_clauses P)))
    (finite_system_interfaces P))"

definition finite_call_alternative_state where
  "finite_call_alternative_state st q r d p z = (case z of (i,c,S,u) \<Rightarrow>
    resolution_state_substitute (finite_binding_substitution u)
      (Resolution_State (finite_clause_goals q d c S |\<union>| (resolution_pending st |-| {|Resolution_Call_Goal q r d p|}))
        (finsert (finite_clause_node q d c S) (resolution_nodes st)) (resolution_witnesses st)))"

lemma fimage_distributes:
  "fimage f (ffUnion (fimage g A)) = ffUnion (fimage (\<lambda>a. fimage f (g a)) A)"
  "fimage f (case x of None \<Rightarrow> B | Some y \<Rightarrow> C y) = (case x of None \<Rightarrow> fimage f B | Some y \<Rightarrow> fimage f (C y))"
  "fimage f (case z of (a,b) \<Rightarrow> D a b) = (case z of (a,b) \<Rightarrow> fimage f (D a b))"
  "fimage f (if b then B else B') = (if b then fimage f B else fimage f B')"
  by (auto simp: fset_eq_iff ffUnion.rep_eq fimage.rep_eq split: option.split prod.split)

lemma finite_call_successors_alternatives:
  "finite_call_successors P st q r d p =
    fimage (finite_call_alternative_state st q r d p) (finite_call_alternative_set P q d p)"
  unfolding finite_call_successors_def finite_call_alternative_set_def
  by (simp add: fimage_distributes finite_call_alternative_state_def split_def cong: if_cong option.case_cong)

definition finite_material_alternative_set where
  "finite_material_alternative_set M = (case finite_material_resolution M of
      Material_Waits \<Rightarrow> {||}
    | Material_Solutions Ws \<Rightarrow> ffUnion (fimage (\<lambda>W. ffUnion (fimage (\<lambda>E.
        case finite_unify_pairs E of None \<Rightarrow> {||} | Some u \<Rightarrow> {|(E,u)|})
      (finite_material_instance_pairs W M))) Ws))"

definition finite_material_alternative_state where
  "finite_material_alternative_state st q r M z = (case z of (E,u) \<Rightarrow> resolution_state_substitute
    (finite_binding_substitution u)
    (Resolution_State (resolution_pending st |-| {|Resolution_Material_Goal q r M|})
      (resolution_nodes st) (resolution_witnesses st)))"

lemma finite_material_successors_alternatives:
  "finite_material_successors st q r M =
    fimage (finite_material_alternative_state st q r M) (finite_material_alternative_set M)"
  unfolding finite_material_successors_def finite_material_alternative_set_def
  by (simp add: fimage_distributes finite_material_alternative_state_def cong: option.case_cong
    split: finite_material_outcome.split)

fun finite_goal_alternatives ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> nat" where
  "finite_goal_alternatives P (Resolution_Call_Goal q r d p) = fcard (finite_call_alternative_set P q d p)"
| "finite_goal_alternatives P (Resolution_Material_Goal q r M) = fcard (finite_material_alternative_set M)"

lemma fcard_one_singleton:
  assumes "fcard A = 1"
  obtains a where "A = {|a|}"
proof -
  have "card (fset A) = 1" using assms by (simp add: fcard.rep_eq)
  then obtain a where "fset A = {a}" by (rule card_1_singletonE)
  then have "A = {|a|}" by (simp add: fset_eq_iff)
  then show thesis by (rule that)
qed

text \<open>
  The contract holds where the goal is not closed by reuse, which gives one successor whatever its alternatives.
\<close>

lemma finite_goal_alternatives_none:
  "\<not> finite_reusable st g \<Longrightarrow> finite_goal_alternatives P g = 0 \<longleftrightarrow> finite_goal_successors P st g = {||}"
  by (cases g) (simp_all add: finite_call_successors_alternatives finite_material_successors_alternatives)

lemma finite_goal_alternatives_one:
  assumes "finite_goal_alternatives P g = 1"
  shows "\<exists>s. finite_goal_successors P st g = {|s|}"
proof (cases "finite_reusable st g")
  case True
  then show ?thesis by (simp add: finite_reusable_successors)
next
  case False
  then show ?thesis
proof (cases g)
  case (Resolution_Call_Goal q r d p)
  have "fcard (finite_call_alternative_set P q d p) = 1" using assms Resolution_Call_Goal by simp
  then obtain a where "finite_call_alternative_set P q d p = {|a|}" by (rule fcard_one_singleton)
  then show ?thesis using False by (simp add: Resolution_Call_Goal finite_call_successors_alternatives)
next
  case (Resolution_Material_Goal q r M)
  have "fcard (finite_material_alternative_set M) = 1" using assms Resolution_Material_Goal by simp
  then obtain a where "finite_material_alternative_set M = {|a|}" by (rule fcard_one_singleton)
  then show ?thesis using False by (simp add: Resolution_Material_Goal finite_material_successors_alternatives)
qed
qed

section \<open>The witness construction\<close>

text \<open>
  A witness construction (W1 of task 496's entry) registers premise-only variables of clauses, named by
  their site and schema, and returns a ground value for a registered variable from the program, the
  site, the clause and the ground bindings of the clause's own variables so far, or nothing. A
  registered variable is never extended by the search: a goal holding it while it is free is held
  back; once every other variable of the goals holding it is ground, the construction is called and
  its value bound.
\<close>

record ('a,'s,'d,'c) finite_witness_construction =
  witness_registered :: "'d \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> 'a fset"
  witness_value :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow>
    ('a \<times> finite_factor_term) fset \<Rightarrow> 'a \<Rightarrow> finite_factor_term option"

definition no_witness_construction :: "('a,'s,'d,'c) finite_witness_construction" where
  "no_witness_construction = \<lparr>witness_registered=(\<lambda>d S. {||}), witness_value=(\<lambda>P d S B a. None)\<rparr>"

text \<open>
  A variable left free when every goal is resolved was constrained by nothing, and takes the empty
  payload; on a ground pattern this reading is the term the pattern presents.
\<close>

fun finite_residual_term :: "'v finite_term_pattern \<Rightarrow> finite_factor_term" where
  "finite_residual_term (Finite_Variable v) = Finite_Payload []"
| "finite_residual_term (Finite_Pattern_Target t) = Finite_Target t"
| "finite_residual_term (Finite_Pattern_Payload v) = Finite_Payload v"
| "finite_residual_term (Finite_Pattern_Pair p q) = Finite_Pair (finite_residual_term p) (finite_residual_term q)"

definition finite_node_ground_bindings ::
    "('a,'s,'d,'c) resolution_node \<Rightarrow> ('a \<times> finite_factor_term) fset" where
  "finite_node_ground_bindings nd = fimage (\<lambda>(a,p). (a,finite_residual_term p))
    (ffilter (\<lambda>(a,p). finite_pattern_variables p={||}) (resolution_node_bindings nd))"

definition finite_free_registered ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a fset" where
  "finite_free_registered \<kappa> nd = ffilter
    (\<lambda>a. (a,Finite_Variable ((resolution_node_position nd,True),a)) |\<in>| resolution_node_bindings nd)
    (witness_registered \<kappa> (resolution_node_site nd) (resolution_node_schema nd))"

definition finite_goal_holders ::
    "('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('s,'a) resolution_variable \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_goal_holders G x = ffilter (\<lambda>g. x |\<in>| resolution_goal_variables g) G"

definition finite_registration_ready ::
    "('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> bool" where
  "finite_registration_ready G nd a = (let x = ((resolution_node_position nd,True),a); H = finite_goal_holders G x in
    H \<noteq> {||} \<and> fBall H (\<lambda>g. resolution_goal_variables g |\<subseteq>| {|x|}))"

definition finite_registered_value ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a \<Rightarrow> finite_factor_term option" where
  "finite_registered_value \<kappa> P nd a =
    witness_value \<kappa> P (resolution_node_site nd) (resolution_node_schema nd) (finite_node_ground_bindings nd) a"

definition finite_constructed ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 'a fset" where
  "finite_constructed \<kappa> P G nd = ffilter
    (\<lambda>a. finite_registration_ready G nd a \<and> finite_registered_value \<kappa> P nd a \<noteq> None) (finite_free_registered \<kappa> nd)"

definition finite_held ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_held \<kappa> st g = fBex (resolution_nodes st) (\<lambda>nd. fBex (finite_free_registered \<kappa> nd)
    (\<lambda>a. ((resolution_node_position nd,True),a) |\<in>| resolution_goal_variables g))"

definition finite_construction_substitution ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow>
      ('s,'a) resolution_variable \<Rightarrow> ('s,'a) resolution_variable finite_term_pattern" where
  "finite_construction_substitution \<kappa> P G nd z = (case z of ((q,b),a) \<Rightarrow>
    if b \<and> q=resolution_node_position nd \<and> a |\<in>| finite_constructed \<kappa> P G nd then
      (case finite_registered_value \<kappa> P nd a of Some v \<Rightarrow> finite_exact_term_pattern v | None \<Rightarrow> Finite_Variable z)
    else Finite_Variable z)"

definition finite_construction_step ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_construction_step \<kappa> P st nd = (let G = resolution_pending st in
    resolution_state_substitute (finite_construction_substitution \<kappa> P G nd)
      (Resolution_State G (resolution_nodes st) (resolution_witnesses st |\<union>|
        ffUnion (fimage (\<lambda>a. case finite_registered_value \<kappa> P nd a of
            Some v \<Rightarrow> {|(((resolution_node_position nd,True),a),v)|} | None \<Rightarrow> {||})
          (finite_constructed \<kappa> P G nd)))))"

section \<open>Selection\<close>

text \<open>
  A registered variable ready for its construction is constructed before any goal, and a goal holding a
  free registered variable is not selected. Among the other pending goals that are calls or material goals
  R1 can solve (the candidates), selection takes in order (F1 of the addition "The resolver at the given's
  size" to task 495's entry): a goal the search settles at once — with no alternative, pruned, or closed by reuse
  (F3); a goal a priority names; a goal with one alternative; then R3's classes, reading a goal's groundness and
  where its variables occur — a ground goal, a call goal whose free variables occur in no other pending goal, a
  material goal R1 can solve, a call goal with a ground part — where a ground call equal to a pending goal at a lesser
  position, or to the call of a node that is not its ancestor and whose subtree is not solved, waits while another
  goal of these classes stands. Within the first nonempty class the goal at the least position is taken: positions
  are socket paths, and the order of sockets orders which goal is worked first, never which alternative is kept.
  R3's default is the selection at the empty priority.
\<close>

fun finite_position_less :: "'s::linorder list \<Rightarrow> 's list \<Rightarrow> bool" where
  "finite_position_less [] (y#ys) = True"
| "finite_position_less (x#xs) (y#ys) = (x<y \<or> x=y \<and> finite_position_less xs ys)"
| "finite_position_less xs ys = False"

text \<open>The order of positions is a strict total order, prefixes first.\<close>

lemma finite_position_less_irrefl: "\<not> finite_position_less p p"
  by (induction p) auto

lemma finite_position_less_trans:
  "finite_position_less p q \<Longrightarrow> finite_position_less q r \<Longrightarrow> finite_position_less p r"
proof (induction p arbitrary: q r)
  case Nil
  then obtain z zs where "r=z#zs" by (cases q; cases r) auto
  then show ?case by simp
next
  case (Cons x xs)
  obtain y ys where q: "q=y#ys" using Cons.prems(1) by (cases q) auto
  obtain z zs where r: "r=z#zs" using Cons.prems(2) q by (cases r) auto
  show ?case using Cons.prems Cons.IH[of ys zs] unfolding q r by auto
qed

lemma finite_position_less_total: "p\<noteq>q \<Longrightarrow> finite_position_less p q \<or> finite_position_less q p"
proof (induction p arbitrary: q)
  case Nil
  then show ?case by (cases q) auto
next
  case (Cons x xs)
  show ?case
  proof (cases q)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    show ?thesis using Cons.IH[of ys] Cons.prems unfolding Cons by (cases "x<y"; cases "y<x") auto
  qed
qed

definition finite_first_goals ::
    "('a,'s::linorder,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_first_goals G = ffilter (\<lambda>g. \<not> fBex G (\<lambda>h.
    finite_position_less (resolution_goal_position h) (resolution_goal_position g))) G"

definition finite_first_nodes ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_first_nodes N = ffilter (\<lambda>nd. \<not> fBex N (\<lambda>m.
    finite_position_less (resolution_node_position m) (resolution_node_position nd))) N"

fun finite_pattern_has_leaf :: "'v finite_term_pattern \<Rightarrow> bool" where
  "finite_pattern_has_leaf (Finite_Variable v) = False"
| "finite_pattern_has_leaf (Finite_Pattern_Target t) = True"
| "finite_pattern_has_leaf (Finite_Pattern_Payload v) = True"
| "finite_pattern_has_leaf (Finite_Pattern_Pair p q) = (finite_pattern_has_leaf p \<or> finite_pattern_has_leaf q)"

fun finite_ground_call_goal :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_ground_call_goal (Resolution_Call_Goal q r d p) = (finite_pattern_variables p={||})"
| "finite_ground_call_goal (Resolution_Material_Goal q r M) = False"

fun finite_leaf_call_goal :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_leaf_call_goal (Resolution_Call_Goal q r d p) = finite_pattern_has_leaf p"
| "finite_leaf_call_goal (Resolution_Material_Goal q r M) = False"

fun finite_solvable_material_goal :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_solvable_material_goal (Resolution_Call_Goal q r d p) = False"
| "finite_solvable_material_goal (Resolution_Material_Goal q r M) = (finite_material_resolution M \<noteq> Material_Waits)"

definition finite_independent_goal ::
    "('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_independent_goal G g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> finite_pattern_variables p\<noteq>{||} \<and>
        fBall G (\<lambda>h. h=g \<or> resolution_goal_variables h |\<inter>| resolution_goal_variables g={||})
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

definition finite_goal_selection ::
    "('a,'s::linorder,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset" where
  "finite_goal_selection G A = (let c1 = ffilter finite_ground_call_goal A;
      c2 = ffilter (finite_independent_goal G) A; c3 = ffilter finite_solvable_material_goal A;
      c4 = ffilter finite_leaf_call_goal A in
    finite_first_goals (if c1\<noteq>{||} then c1 else if c2\<noteq>{||} then c2 else if c3\<noteq>{||} then c3 else c4))"

fun resolution_is_call :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "resolution_is_call (Resolution_Call_Goal q r d p) = True"
| "resolution_is_call (Resolution_Material_Goal q r M) = False"

definition finite_candidate_goal :: "('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_candidate_goal g \<longleftrightarrow> resolution_is_call g \<or> finite_solvable_material_goal g"

lemma finite_candidate_goal_simps [simp]:
  "finite_candidate_goal (Resolution_Call_Goal q r d p)"
  "finite_candidate_goal (Resolution_Material_Goal q' r' M) \<longleftrightarrow> finite_material_resolution M \<noteq> Material_Waits"
  by (simp_all add: finite_candidate_goal_def)

lemma finite_goal_selection_candidate:
  "g |\<in>| finite_goal_selection G A \<Longrightarrow> g |\<in>| A \<and> finite_candidate_goal g"
  unfolding finite_goal_selection_def Let_def finite_first_goals_def
  by (cases g) (auto simp: finite_independent_goal_def split: if_splits)

text \<open>
  A ground call goal equal to the call of an ancestor on its branch is pruned; the search ends its branch there.
\<close>

definition finite_pruned :: "('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_pruned st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> finite_pattern_variables p={||} \<and> fBex (resolution_nodes st) (\<lambda>nd.
        length (resolution_node_position nd)<length q \<and>
        take (length (resolution_node_position nd)) q=resolution_node_position nd \<and>
        resolution_node_site nd=d \<and> resolution_node_call nd=p)
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

text \<open>
  The waiting rule (F3): a ground call equal to a pending call at a lesser position, or to the call of a node that is
  not its ancestor and whose subtree is not solved, waits, so that its equal occurrence is solved first and closes it.
\<close>

definition finite_goal_waits ::
    "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool" where
  "finite_goal_waits st g = (case g of
      Resolution_Call_Goal q r d p \<Rightarrow> finite_pattern_variables p={||} \<and>
        (fBex (resolution_pending st) (\<lambda>h. case h of
            Resolution_Call_Goal q' r' d' p' \<Rightarrow> d'=d \<and> p'=p \<and> finite_position_less q' q
          | Resolution_Material_Goal q' r' M \<Rightarrow> False) \<or>
         fBex (resolution_nodes st) (\<lambda>nd. resolution_node_site nd=d \<and> resolution_node_call nd=p \<and>
           take (length (resolution_node_position nd)) q \<noteq> resolution_node_position nd \<and> \<not> finite_solved_node st nd))
    | Resolution_Material_Goal q r M \<Rightarrow> False)"

definition finite_waiting_selection ::
    "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_waiting_selection st G A = (let W = finite_goal_selection G (ffilter (\<lambda>g. \<not> finite_goal_waits st g) A) in
    if W \<noteq> {||} then W else finite_goal_selection G A)"

lemma finite_waiting_selection_candidate:
  "g |\<in>| finite_waiting_selection st G A \<Longrightarrow> g |\<in>| A \<and> finite_candidate_goal g"
  using finite_goal_selection_candidate[of g G A]
    finite_goal_selection_candidate[of g G "ffilter (\<lambda>g. \<not> finite_goal_waits st g) A"]
  by (auto simp: finite_waiting_selection_def Let_def split: if_splits)

text \<open>The waiting rule never empties the selection R3's classes make.\<close>

lemma finite_waiting_selection_nonempty:
  "finite_goal_selection G A \<noteq> {||} \<Longrightarrow> finite_waiting_selection st G A \<noteq> {||}"
  by (simp add: finite_waiting_selection_def Let_def)

text \<open>
  The choice among the unheld pending goals A of the pending goals G at a priority: the alternatives of each candidate
  are counted once, and each class is formed only when the classes before it are empty.
\<close>

definition finite_goal_choice ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset \<Rightarrow> ('a,'s,'d,'c) resolution_goal fset" where
  "finite_goal_choice pr P st G A = (let C = ffilter finite_candidate_goal A;
      K = fimage (\<lambda>g. (finite_goal_alternatives P g,g)) C;
      c0 = fimage snd (ffilter (\<lambda>z. fst z = 0 \<or> finite_pruned st (snd z) \<or> finite_reusable st (snd z)) K) in
    if c0 \<noteq> {||} then finite_first_goals c0
    else let cp = ffilter (pr st) C in if cp \<noteq> {||} then finite_first_goals cp
    else let c1 = fimage snd (ffilter (\<lambda>z. fst z = 1) K) in if c1 \<noteq> {||} then finite_first_goals c1
    else finite_waiting_selection st G A)"

lemma finite_goal_choice_candidate:
  "g |\<in>| finite_goal_choice pr P st G A \<Longrightarrow> g |\<in>| A \<and> finite_candidate_goal g"
  unfolding finite_goal_choice_def Let_def
  using finite_waiting_selection_candidate[of g st G A]
  by (auto simp: finite_first_goals_def fimage.rep_eq ffilter.rep_eq split: if_splits)

datatype ('a,'s,'d,'c) resolution_selection =
    Select_Construction "('a,'s,'d,'c) resolution_node fset"
  | Select_Goals "('a,'s,'d,'c) resolution_goal fset"
  | Select_None

definition finite_resolution_select_at ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_resolution_select_at pr \<kappa> P st = (let G = resolution_pending st;
      N = ffilter (\<lambda>nd. finite_constructed \<kappa> P G nd\<noteq>{||}) (resolution_nodes st) in
    if N\<noteq>{||} then Select_Construction (finite_first_nodes N)
    else let S = finite_goal_choice pr P st G (ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) G) in
      if S={||} then Select_None else Select_Goals S)"

abbreviation finite_resolution_select ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection" where
  "finite_resolution_select \<kappa> P \<equiv> finite_resolution_select_at (\<lambda>st g. False) \<kappa> P"

text \<open>
  At every priority the selection selects a nonempty set of pending, unheld candidates, and a construction exactly
  where R3's default does: the premises of the liftings, whatever the priority names.
\<close>

lemma finite_resolution_select_at_exact:
  shows "finite_resolution_select_at pr \<kappa> P st = Select_Goals G \<Longrightarrow> G \<noteq> {||} \<and>
      (\<forall>g. g |\<in>| G \<longrightarrow> g |\<in>| resolution_pending st \<and> \<not> finite_held \<kappa> st g \<and> finite_candidate_goal g)"
    and "finite_resolution_select_at pr \<kappa> P st = Select_Construction N \<longleftrightarrow>
      finite_resolution_select \<kappa> P st = Select_Construction N"
  subgoal
    using finite_goal_choice_candidate[of _ pr P st "resolution_pending st"
      "ffilter (\<lambda>g. \<not> finite_held \<kappa> st g) (resolution_pending st)"]
    by (auto simp: finite_resolution_select_at_def Let_def split: if_splits)
  subgoal by (auto simp: finite_resolution_select_at_def Let_def split: if_splits)
  done

definition finite_plain_selection ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_goal \<Rightarrow> bool) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_selection" where
  "finite_plain_selection pr P st = (let G = resolution_pending st; S = finite_goal_choice pr P st G G in
    if S={||} then Select_None else Select_Goals S)"

section \<open>The search\<close>

text \<open>
  A ground call goal equal to the call of an ancestor on its branch is pruned (@{const finite_pruned}), checked
  before its successors, among which a ground call closed by reuse has one. A goal with no
  alternative ends its branch: a refutation of the branch, unless a construction supplied a value on
  it, when the branch is unresolved and its diagnosis names the values and the goal refuted at them.
  The bound cuts a branch whose goals are still pending; a branch whose pending goals none can be
  selected is stuck. Every alternative is explored and the outcomes are joined as sets.
\<close>

datatype ('a,'s,'d,'c) resolution_diagnosis =
    Resolution_Cut "('a,'s,'d,'c) resolution_goal fset"
  | Resolution_Stuck "('a,'s,'d,'c) resolution_goal fset"
  | Resolution_Witnessed "(('s,'a) resolution_variable \<times> finite_factor_term) fset" "('a,'s,'d,'c) resolution_goal"
  | Resolution_Refused "('a,'s,'c) finite_schema_proof"
  | Resolution_Unconstructed 'd "('a,'s,'d) finite_factor_schema" 'a "('a,'s,'d,'c) resolution_goal fset"

datatype ('a,'s,'d,'c) resolution_outcome = Resolution_Outcome
  (resolution_found: "('a,'s,'d,'c) resolution_state fset")
  (resolution_diagnoses: "('a,'s,'d,'c) resolution_diagnosis fset")

definition finite_outcome_union ::
    "('a,'s,'d,'c) resolution_outcome fset \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_outcome_union Os = Resolution_Outcome (ffUnion (fimage resolution_found Os))
    (ffUnion (fimage resolution_diagnoses Os))"

text \<open>
  A registered variable ready for its construction for which the construction returns nothing keeps the
  goals holding it back; when no goal can be selected, the diagnosis names each such registration — its
  site, its clause's schema and its variable — with the goals held at it.
\<close>

definition finite_unconstructed ::
    "('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_diagnosis fset" where
  "finite_unconstructed \<kappa> P st = (let G = resolution_pending st in ffUnion (fimage (\<lambda>nd.
    fimage (\<lambda>a. Resolution_Unconstructed (resolution_node_site nd) (resolution_node_schema nd) a
        (finite_goal_holders G ((resolution_node_position nd,True),a)))
      (ffilter (\<lambda>a. finite_registration_ready G nd a \<and> finite_registered_value \<kappa> P nd a=None)
        (finite_free_registered \<kappa> nd)))
    (resolution_nodes st)))"

definition finite_goal_outcome ::
    "(('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome) \<Rightarrow>
      ('a,'s::linorder,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) resolution_state \<Rightarrow>
      ('a,'s,'d,'c) resolution_goal \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_goal_outcome rec P st g = (if finite_pruned st g then Resolution_Outcome {||} {||} else
    let S = finite_goal_successors P st g in
    if S={||} then (if resolution_witnesses st={||} then Resolution_Outcome {||} {||}
      else Resolution_Outcome {||} {|Resolution_Witnessed (resolution_witnesses st) g|})
    else finite_outcome_union (fimage rec S))"

primrec finite_resolution_search_by ::
    "(('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_selection) \<Rightarrow>
      ('a,'s,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_resolution_search_by sel \<kappa> P 0 st = (if resolution_pending st={||}
    then Resolution_Outcome {|st|} {||} else Resolution_Outcome {||} {|Resolution_Cut (resolution_pending st)|})"
| "finite_resolution_search_by sel \<kappa> P (Suc n) st = (if resolution_pending st={||}
    then Resolution_Outcome {|st|} {||} else (case sel st of
      Select_Construction N \<Rightarrow> finite_outcome_union
        (fimage (finite_resolution_search_by sel \<kappa> P n) (fimage (finite_construction_step \<kappa> P st) N))
    | Select_Goals G \<Rightarrow> finite_outcome_union (fimage (finite_goal_outcome (finite_resolution_search_by sel \<kappa> P n) P st) G)
    | Select_None \<Rightarrow> Resolution_Outcome {||}
        (finsert (Resolution_Stuck (resolution_pending st)) (finite_unconstructed \<kappa> P st))))"

definition finite_resolution_search ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow> nat \<Rightarrow>
      ('a,'s,'d,'c) resolution_state \<Rightarrow> ('a,'s,'d,'c) resolution_outcome" where
  "finite_resolution_search \<kappa> P = finite_resolution_search_by (finite_resolution_select \<kappa> P) \<kappa> P"

section \<open>The empty construction\<close>

text \<open>
  The construction registered for nothing holds no goal and constructs nothing: the search selects among
  the pending goals alone.
\<close>

lemma no_witness_free_registered [simp]: "finite_free_registered no_witness_construction nd={||}"
  by (simp add: finite_free_registered_def no_witness_construction_def fset_eq_iff)

lemma no_witness_constructed [simp]: "finite_constructed no_witness_construction P G nd={||}"
  by (simp add: finite_constructed_def fset_eq_iff)

lemma no_witness_held [simp]: "\<not> finite_held no_witness_construction st g"
  by (simp add: finite_held_def)

theorem no_witness_selection:
  "finite_resolution_select_at pr no_witness_construction P st = finite_plain_selection pr P st"
proof -
  have "ffilter (\<lambda>g. \<not> finite_held no_witness_construction st g) (resolution_pending st) = resolution_pending st"
    by (simp add: fset_eq_iff)
  then show ?thesis by (simp add: finite_resolution_select_at_def finite_plain_selection_def Let_def)
qed

lemma finite_resolution_select_none_construction:
  "finite_resolution_select_at pr no_witness_construction P st \<noteq> Select_Construction N"
  by (simp add: no_witness_selection finite_plain_selection_def Let_def)

theorem no_witness_search:
  "finite_resolution_search no_witness_construction P =
    finite_resolution_search_by (finite_plain_selection (\<lambda>st g. False) P) no_witness_construction P"
proof -
  have "finite_resolution_select no_witness_construction P = finite_plain_selection (\<lambda>st g. False) P"
    by (rule ext) (rule no_witness_selection)
  then show ?thesis by (simp add: finite_resolution_search_def)
qed

section \<open>The ground certificate and the result per call\<close>

text \<open>
  A branch with no pending goal gives a certificate: at each node the clause key, the complete ground
  bindings of the clause's own variables, residual variables at the empty payload, and at each premise socket
  the certificate of the node at the socket's position or, where none stands (a ground call closed by reuse), of
  the node at the least position left of the socket whose call is the premise's instance and whose site the
  premise's: the certificate is the unfolded derivation, and its soundness the checker's.
\<close>

definition finite_node_values :: "('a,'s,'d,'c) resolution_node \<Rightarrow> ('a \<times> finite_factor_term) fset" where
  "finite_node_values nd = fimage (\<lambda>(a,p). (a,finite_residual_term p)) (resolution_node_bindings nd)"

definition finite_premise_nodes ::
    "('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow>
      'a finite_term_pattern \<Rightarrow> ('a,'s,'d,'c) resolution_node fset" where
  "finite_premise_nodes N nd s e p = (let q = resolution_node_position nd@[s];
      F = ffilter (\<lambda>m. resolution_node_site m=e \<and>
        finite_residual_term (resolution_node_call m) |\<in>| finite_pattern_instances (finite_node_values nd) p) N;
      C = ffilter (\<lambda>m. resolution_node_position m=q) F in
    if C \<noteq> {||} then C else finite_first_nodes (ffilter (\<lambda>m. finite_position_left (resolution_node_position m) q) F))"

primrec finite_node_proof ::
    "nat \<Rightarrow> ('a,'s::linorder,'d,'c) resolution_node fset \<Rightarrow> ('a,'s,'d,'c) resolution_node \<Rightarrow> ('a,'s,'c) finite_schema_proof" where
  "finite_node_proof 0 N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd) {||}"
| "finite_node_proof (Suc k) N nd = Schema_Proof (resolution_node_clause nd) (finite_node_values nd)
    (ffUnion (fimage (\<lambda>(s,e,p). fimage (\<lambda>m. (s,finite_node_proof k N m)) (finite_premise_nodes N nd s e p))
      (finite_schema_premises (resolution_node_schema nd))))"

text \<open>
  A nonempty set of nodes at distinct positions has one node at its least position.
\<close>

lemma finite_first_nodes_single:
  assumes nonempty: "N \<noteq> {||}"
    and distinct: "\<And>m m'. m |\<in>| N \<Longrightarrow> m' |\<in>| N \<Longrightarrow> resolution_node_position m=resolution_node_position m' \<Longrightarrow> m=m'"
  shows "\<exists>m. finite_first_nodes N = {|m|}"
proof -
  have "\<forall>A. A |\<subseteq>| N \<longrightarrow> A \<noteq> {||} \<longrightarrow>
      (\<exists>m. m |\<in>| A \<and> \<not> fBex A (\<lambda>m'. finite_position_less (resolution_node_position m') (resolution_node_position m)))"
  proof (intro allI)
    fix A show "A |\<subseteq>| N \<longrightarrow> A \<noteq> {||} \<longrightarrow>
        (\<exists>m. m |\<in>| A \<and> \<not> fBex A (\<lambda>m'. finite_position_less (resolution_node_position m') (resolution_node_position m)))"
    proof (induction A rule: fset_induct)
      case empty
      then show ?case by simp
    next
      case (insert x A)
      show ?case
      proof (intro impI)
        assume sub: "finsert x A |\<subseteq>| N"
        show "\<exists>m. m |\<in>| finsert x A \<and> \<not> fBex (finsert x A)
            (\<lambda>m'. finite_position_less (resolution_node_position m') (resolution_node_position m))"
        proof (cases "A={||}")
          case True
          then show ?thesis by (auto simp: finite_position_less_irrefl)
        next
          case False
          then obtain m where m: "m |\<in>| A" and min: "\<not> fBex A (\<lambda>m'. finite_position_less
              (resolution_node_position m') (resolution_node_position m))" using insert.IH sub by auto
          show ?thesis
          proof (cases "finite_position_less (resolution_node_position x) (resolution_node_position m)")
            case True
            have "\<not> finite_position_less (resolution_node_position y) (resolution_node_position x)" if "y |\<in>| A" for y
              using min that finite_position_less_trans[OF _ True] by blast
            then show ?thesis using finite_position_less_irrefl by auto
          next
            case False
            then show ?thesis using m min by auto
          qed
        qed
      qed
    qed
  qed
  then obtain m where m: "m |\<in>| N"
    and min: "\<not> fBex N (\<lambda>m'. finite_position_less (resolution_node_position m') (resolution_node_position m))"
    using nonempty by blast
  have "finite_first_nodes N = {|m|}"
  proof (rule fset_eqI, rule iffI)
    fix y assume y: "y |\<in>| finite_first_nodes N"
    then have yN: "y |\<in>| N" and ymin: "\<not> finite_position_less (resolution_node_position m) (resolution_node_position y)"
      using m by (auto simp: finite_first_nodes_def)
    have "resolution_node_position y=resolution_node_position m"
      using finite_position_less_total[of "resolution_node_position y" "resolution_node_position m"] min yN ymin by blast
    then show "y |\<in>| {|m|}" using distinct[OF yN m] by simp
  next
    fix y assume "y |\<in>| {|m|}"
    then show "y |\<in>| finite_first_nodes N" using m min by (simp add: finite_first_nodes_def)
  qed
  then show ?thesis by blast
qed

definition finite_state_proofs :: "('a,'s::linorder,'d,'c) resolution_state \<Rightarrow> ('a,'s,'c) finite_schema_proof fset" where
  "finite_state_proofs st = fimage (finite_node_proof (fcard (resolution_nodes st)) (resolution_nodes st))
    (ffilter (\<lambda>nd. resolution_node_position nd=[]) (resolution_nodes st))"

definition finite_initial_state :: "'d \<Rightarrow> finite_factor_term \<Rightarrow> ('a,'s,'d,'c) resolution_state" where
  "finite_initial_state d t = Resolution_State {|Resolution_Call_Goal [] None d (finite_exact_term_pattern t)|} {||} {||}"

datatype ('a,'s,'d,'c) finite_resolution_result =
    Finite_Resolved "('a,'s,'c) finite_schema_proof fset"
  | Finite_Refuted
  | Finite_Unresolved "('a,'s,'d,'c) resolution_diagnosis fset"

text \<open>
  The result for a call: resolved with the certificates of its successful branches that the finite
  proof checker accepts; refuted when no branch succeeded and none was cut, stuck or refuted at a
  constructed value; unresolved otherwise, with its diagnosis, which also keeps a certificate the checker
  refused.
\<close>

definition finite_program_resolution ::
    "('a,'s::linorder,'d,'c) finite_witness_construction \<Rightarrow> ('a,'s,'d,'c) finite_schema_system \<Rightarrow>
      'd \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> ('a,'s,'d,'c) finite_resolution_result" where
  "finite_program_resolution \<kappa> P d t n = (let R = finite_resolution_search \<kappa> P n (finite_initial_state d t);
      C = ffUnion (fimage finite_state_proofs (resolution_found R));
      A = ffilter (\<lambda>p. finite_checks_schema_proof P p d t) C in
    if A\<noteq>{||} then Finite_Resolved A
    else if resolution_diagnoses R={||} \<and> C={||} then Finite_Refuted
    else Finite_Unresolved (resolution_diagnoses R |\<union>| fimage Resolution_Refused C))"

section \<open>Soundness through the finite proof checker\<close>

text \<open>
  Every certificate of a resolved call is accepted by the existing finite proof checker, whatever
  construction supplied the values in its bindings; the call then holds in the program's positive
  meaning by the checker's exactness and the soundness of schema proofs. Soundness is the checker's.
\<close>

theorem finite_program_resolution_accepted:
  assumes "finite_program_resolution \<kappa> P d t n = Finite_Resolved C" and "p |\<in>| C"
  shows "finite_checks_schema_proof P p d t"
  using assms unfolding finite_program_resolution_def Let_def by (auto split: if_splits)

theorem finite_program_resolution_sound:
  assumes res: "finite_program_resolution \<kappa> P d t n = Finite_Resolved C"
  shows "C\<noteq>{||}" and "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)"
proof -
  show nonempty: "C\<noteq>{||}" using res unfolding finite_program_resolution_def Let_def by (auto split: if_splits)
  then obtain p where member: "p |\<in>| C" by (metis all_not_fin_conv)
  have "finite_checks_schema_proof P p d t" by (rule finite_program_resolution_accepted[OF res member])
  then have "checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
    by (simp only: finite_checks_schema_proof_exact)
  then show "(d,decode_finite_term t) \<in> positive_meaning (decode_finite_system P)" by (rule schema_proof_sound)
qed

theorem finite_program_resolution_refuted:
  "finite_program_resolution \<kappa> P d t n = Finite_Refuted \<longleftrightarrow>
    (let R = finite_resolution_search \<kappa> P n (finite_initial_state d t) in
      ffUnion (fimage finite_state_proofs (resolution_found R))={||} \<and> resolution_diagnoses R={||})"
  unfolding finite_program_resolution_def Let_def by auto

export_code finite_program_resolution no_witness_construction checking SML

end
