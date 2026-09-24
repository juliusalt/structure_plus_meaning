theory Development_State_Rows
imports Isabelle_Local_Names Development_Constant_Verification
begin

section \<open>A state's own rows, as the verdict reads them\<close>

text \<open>
  The verdict of a kind reads five things of an entity: its kind, the constant it declares, the
  constants it is a statement of, the constants it mentions, and its identity across two states.
  It reads nothing inside a statement. This theory presents a checked state as exactly that much
  structure — the relational skeleton of a state and no more — and states the relation between a
  state and such a presentation, so that every field of the verdict reads the state through it.

  A constant is an atom carrying its name as an inert payload, and every reference to a constant
  is a citation of that atom, so a name-table position never appears on the presented side. There
  is one entity family per kind of the entity language and one family for the roots. A row holds
  the keys of the atoms it cites and its identity, the local presentation of its own value, carried
  inert: the verdict uses no structure of a statement, only its identity, and a carried identity is
  compared only as a whole. \<open>isabelle_local_entities_renamed\<close> already proves that identity invariant
  under every correspondence of tables, which is what lets rows of two states be compared by their
  keys alone, and it is consumed here, not proved again.

  What the presentation carries and what a program computes are kept apart. The conditions below
  are premises of the relation: keys distinct and determined by identity, one family per kind
  holding exactly the entities of that kind, declared, subjects and mentions the keys of the
  corresponding atoms, the roots as a family, distinct names, single-valued stores, and no
  reference outside the state's atoms. Three consequences are derived here as lemmas with the owner
  of their premise named, so that the tasks after this one consume them instead of assuming them
  silently. That the state's names are distinct, the verdict's ninth field, is carried as a premise
  of \<open>atoms_present\<close>; for an answer state it is established by the answer's reader, which must
  refuse a duplicated name. That its unknown positions are vacuous follows because a reference is a
  citation of an atom; its owner is the presentation, through the carried inclusion of the state's
  positions in its table. That its roots are distinct as local presentations follows from the root
  family's distinct keys and their self-agreement; its owner is the exporter that defines the
  state's roots, from which an answer state is exported too.
\<close>

subsection \<open>The kinds of the entity language index the families of a presented state\<close>

text \<open>
  A kind is the family that holds a row, never a datum the row carries: no relation below reads a
  tag inside a row to tell what kind it is. The kinds are the constructors of the entity language,
  read on the source side alone, to say which family holds which entity.
\<close>

datatype entity_kind =
  Base_Kind | Development_Kind | Frontier_Kind
| Definition_Kind | Specification_Kind | Equation_Kind

fun entity_kind_of :: "isabelle_entity \<Rightarrow> entity_kind" where
  "entity_kind_of (Isabelle_Base_Constant t)=Base_Kind"
| "entity_kind_of (Isabelle_Development_Constant t)=Development_Kind"
| "entity_kind_of (Isabelle_Frontier_Constant t)=Frontier_Kind"
| "entity_kind_of (Isabelle_Definition p)=Definition_Kind"
| "entity_kind_of (Isabelle_Specification p)=Specification_Kind"
| "entity_kind_of (Isabelle_Code_Equation p)=Equation_Kind"

lemma entity_kind_of_renamed [simp]: "entity_kind_of (isabelle_entity_rename f e)=entity_kind_of e"
  by (cases e) simp_all

text \<open>The kinds are listed once, so that the selection of every family of a state is a list of its families.\<close>

definition entity_kinds :: "entity_kind list" where
  "entity_kinds=[Base_Kind,Development_Kind,Frontier_Kind,Definition_Kind,Specification_Kind,Equation_Kind]"

lemma entity_kinds_member [simp]: "k\<in>set entity_kinds"
  by (cases k) (simp_all add: entity_kinds_def)

lemma entity_kinds_all: "set entity_kinds=UNIV"
  by auto


subsection \<open>The carriers: atoms, rows and families\<close>

text \<open>
  A key is a path, as the keys of readiness's rows and of the reach's table are. A family is that
  path keyed to its row; the atoms are that path keyed to an inert name. A row is parameterized by
  the presentation of its own value, since an entity row carries an entity's local presentation and
  a root row a term's; nothing else distinguishes the two.
\<close>

type_synonym state_key = "bool list"

record 'i state_row =
  row_declared :: "state_key list"
  row_subjects :: "state_key list"
  row_mentions :: "state_key list"
  row_identity :: 'i

type_synonym 'i state_family = "(state_key\<times>'i state_row) list"

record state_rows =
  state_atoms :: "(state_key\<times>String.literal) list"
  state_entities :: "entity_kind \<Rightarrow> isabelle_context state_family"
  state_roots :: "(String.literal list\<times>isabelle_term) state_family"

definition presented_rows :: "state_rows \<Rightarrow> (state_key\<times>isabelle_context state_row) set" where
  "presented_rows R=(\<Union>k. set (state_entities R k))"

lemma presented_rows_member: "(a,p)\<in>set (state_entities R k) \<Longrightarrow> (a,p)\<in>presented_rows R"
  by (auto simp: presented_rows_def)

lemma presented_rows_family:
  assumes "(a,p)\<in>presented_rows R"
  obtains k where "(a,p)\<in>set (state_entities R k)"
  using assms by (auto simp: presented_rows_def)

text \<open>
  Every family of a state, each kind's once: the selection of every family is a list of its families, read
  over the kinds as they are listed.
\<close>

definition state_all_families :: "state_rows \<Rightarrow> isabelle_context state_family list" where
  "state_all_families R=map (state_entities R) entity_kinds"

lemma state_all_families_range: "set (state_all_families R)=range (state_entities R)"
  by (simp add: state_all_families_def entity_kinds_all)

lemma state_all_families_rows: "(\<Union>F\<in>set (state_all_families R). set F)=presented_rows R"
  by (auto simp: state_all_families_def presented_rows_def)

lemma state_all_families_found:
  "(\<exists>F\<in>set (state_all_families R). \<exists>p. (a,p)\<in>set F) \<longleftrightarrow> (\<exists>p. (a,p)\<in>presented_rows R)"
proof
  assume "\<exists>F\<in>set (state_all_families R). \<exists>p. (a,p)\<in>set F"
  then show "\<exists>p. (a,p)\<in>presented_rows R" by (auto simp: state_all_families_def presented_rows_def)
next
  assume "\<exists>p. (a,p)\<in>presented_rows R"
  then obtain p k where row: "(a,p)\<in>set (state_entities R k)" by (auto simp: presented_rows_def)
  have "state_entities R k\<in>set (state_all_families R)"
    unfolding state_all_families_def set_map by (rule imageI) simp
  then show "\<exists>F\<in>set (state_all_families R). \<exists>p. (a,p)\<in>set F" using row by blast
qed

subsection \<open>Keys agree when the values they key are the same\<close>

text \<open>
  One notion serves both the atoms and the rows: two keyed families agree when a key of the one and
  a key of the other are equal exactly if the values they key are the same value, read by the
  observation that identifies it — a name for an atom, a local presentation for a row. Keys
  distinct and determined by identity is this notion of a family with itself.
\<close>

definition keyed_agree :: "('v \<Rightarrow> 'i) \<Rightarrow> (state_key\<times>'v) set \<Rightarrow> (state_key\<times>'v) set \<Rightarrow> bool" where
  "keyed_agree ident X Y \<longleftrightarrow> (\<forall>a x b y. (a,x)\<in>X \<longrightarrow> (b,y)\<in>Y \<longrightarrow> ((a=b)=(ident x=ident y)))"

lemma keyed_agreeI:
  assumes "\<And>a x b y. (a,x)\<in>X \<Longrightarrow> (b,y)\<in>Y \<Longrightarrow> (a=b)=(ident x=ident y)"
  shows "keyed_agree ident X Y"
  using assms by (simp add: keyed_agree_def)

lemma keyed_agreeD:
  assumes agree: "keyed_agree ident X Y" and left: "(a,x)\<in>X" and right: "(b,y)\<in>Y"
  shows "(a=b)=(ident x=ident y)"
  using agree left right by (simp add: keyed_agree_def)

lemma keyed_agree_symmetric:
  assumes agree: "keyed_agree ident X Y"
  shows "keyed_agree ident Y X"
proof (rule keyed_agreeI)
  fix a x b y assume left: "(a,x)\<in>Y" and right: "(b,y)\<in>X"
  have "(b=a)=(ident y=ident x)" by (rule keyed_agreeD[OF agree right left])
  then show "(a=b)=(ident x=ident y)" by auto
qed

lemma keyed_agree_subsets:
  assumes agree: "keyed_agree ident X Y" and left: "X'\<subseteq>X" and right: "Y'\<subseteq>Y"
  shows "keyed_agree ident X' Y'"
proof (rule keyed_agreeI)
  fix a x b y assume member: "(a,x)\<in>X'" "(b,y)\<in>Y'"
  have "(a,x)\<in>X" using member(1) left by auto
  moreover have "(b,y)\<in>Y" using member(2) right by auto
  ultimately show "(a=b)=(ident x=ident y)" by (rule keyed_agreeD[OF agree])
qed

subsection \<open>What a row of a state cites\<close>

text \<open>
  The three citation families of a row are read from the entity: the constant it declares, the
  constants it is a statement of, and the constants its statement mentions. A declaration cites at
  most one constant and mentions none; a statement declares none. Each is a list of constants on
  the source side, and the keys of their atoms on the presented side. A root cites the constant it
  heads, which is what the state's mentioned constants already take of a root.
\<close>

definition entity_declared :: "isabelle_entity \<Rightarrow> nat list" where
  "entity_declared e=(case isabelle_declared_constant e of None \<Rightarrow> [] | Some c \<Rightarrow> [c])"

definition entity_mentions :: "isabelle_entity \<Rightarrow> nat list" where
  "entity_mentions e=(case isabelle_specified_proposition e of None \<Rightarrow> [] | Some p \<Rightarrow> isabelle_term_constants p)"

definition root_mentions :: "isabelle_term \<Rightarrow> nat list" where
  "root_mentions t=(case isabelle_head_constant t of None \<Rightarrow> [] | Some c \<Rightarrow> [c])"

definition entity_row ::
    "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity \<Rightarrow> isabelle_context state_row" where
  "entity_row key C e=\<lparr>row_declared=map key (entity_declared e),
    row_subjects=map key (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e),
    row_mentions=map key (entity_mentions e),
    row_identity=isabelle_local_entities (fst C) [e]\<rparr>"

definition root_row ::
    "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_context \<Rightarrow> isabelle_term \<Rightarrow> (String.literal list\<times>isabelle_term) state_row" where
  "root_row key C t=\<lparr>row_declared=[],row_subjects=[],row_mentions=map key (root_mentions t),
    row_identity=isabelle_local_root (fst C) t\<rparr>"

definition state_positions :: "isabelle_rooted_context \<Rightarrow> nat set" where
  "state_positions S=(\<Union>e\<in>set (snd (snd S)). set (isabelle_entity_positions e))
    \<union> (\<Union>t\<in>set (fst S). set (isabelle_term_positions t))"

subsection \<open>Every constant a row cites is a position the value itself uses\<close>

text \<open>
  A citation is a reference of the value that cites it. These are the inclusions that make ``no
  reference outside the state's atoms'' a consequence of the one premise that the state's own
  values stay within its table, rather than a separate condition on each citation family.
\<close>

lemma isabelle_term_constants_positions:
  "set (isabelle_term_constants t)\<subseteq>set (isabelle_term_positions t)"
  by (induction t) auto

lemma isabelle_head_constant_positions:
  "isabelle_head_constant t=Some c \<Longrightarrow> c\<in>set (isabelle_term_positions t)"
  by (induction t) auto

lemma isabelle_equation_left_positions:
  "isabelle_equation_left names p=Some l \<Longrightarrow> set (isabelle_term_positions l)\<subseteq>set (isabelle_term_positions p)"
  by (induction names p rule: isabelle_equation_left.induct) (auto split: if_splits)

lemma isabelle_equation_subject_positions:
  assumes subject: "Option.bind (isabelle_equation_left names p) isabelle_head_constant=Some c"
  shows "c\<in>set (isabelle_term_positions p)"
proof -
  obtain l where left: "isabelle_equation_left names p=Some l"
    and head: "isabelle_head_constant l=Some c"
    using subject by (cases "isabelle_equation_left names p") simp_all
  have "c\<in>set (isabelle_term_positions l)" by (rule isabelle_head_constant_positions[OF head])
  then show ?thesis using isabelle_equation_left_positions[OF left] by auto
qed

lemma isabelle_entity_subjects_positions:
  "set (isabelle_entity_subjects names D e)\<subseteq>set (isabelle_entity_positions e)"
proof (cases e)
  case (Isabelle_Specification p)
  then show ?thesis
    using isabelle_term_constants_positions[of p] by (auto simp: isabelle_entity_positions_def)
next
  case (Isabelle_Definition p)
  then show ?thesis
    by (auto simp: isabelle_entity_positions_def split: option.splits
      dest: isabelle_equation_subject_positions isabelle_equation_subject_positions[OF sym])
next
  case (Isabelle_Code_Equation p)
  then show ?thesis
    by (auto simp: isabelle_entity_positions_def split: option.splits
      dest: isabelle_equation_subject_positions isabelle_equation_subject_positions[OF sym])
qed (simp_all add: isabelle_entity_positions_def)

lemma entity_declared_positions:
  "set (entity_declared e)\<subseteq>set (isabelle_entity_positions e)"
  by (cases e)
    (simp_all add: entity_declared_def isabelle_entity_positions_def split: isabelle_term_with.splits)

lemma entity_mentions_positions:
  "set (entity_mentions e)\<subseteq>set (isabelle_entity_positions e)"
  by (cases e)
    (simp_all add: entity_mentions_def isabelle_entity_positions_def isabelle_term_constants_positions)

lemma root_mentions_positions:
  "set (root_mentions t)\<subseteq>set (isabelle_term_positions t)"
  by (auto simp: root_mentions_def isabelle_head_constant_positions split: option.splits)

subsection \<open>The presentation of a state\<close>

text \<open>
  The atoms are the positions of the state's table, each keyed and carrying its name: a name names
  at most one atom, which is the verdict's ninth field, and a key keys at most one atom. The entity
  families hold exactly the entities of their kind, the root family exactly the roots in their
  order, and the rows of each family are keyed once. Nothing here is computed; every clause is a
  condition the presentation carries.
\<close>

definition atoms_present :: "(nat \<Rightarrow> state_key) \<Rightarrow> String.literal list \<Rightarrow> state_rows \<Rightarrow> bool" where
  "atoms_present key names R \<longleftrightarrow>
    set (state_atoms R)=(\<lambda>i. (key i,names!i)) ` {..<length names} \<and>
    length (state_atoms R)=length names \<and>
    distinct (map fst (state_atoms R)) \<and> distinct (map snd (state_atoms R))"

definition rows_present :: "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_context \<Rightarrow> state_rows \<Rightarrow> bool" where
  "rows_present key C R \<longleftrightarrow>
    (\<forall>k. set (map snd (state_entities R k))=entity_row key C ` {e\<in>set (snd C). entity_kind_of e=k}) \<and>
    (\<forall>k. distinct (map fst (state_entities R k)))"

definition roots_present ::
    "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_context \<Rightarrow> isabelle_term list \<Rightarrow> state_rows \<Rightarrow> bool" where
  "roots_present key C roots R \<longleftrightarrow>
    map snd (state_roots R)=map (root_row key C) roots \<and> distinct (map fst (state_roots R))"

definition state_presents :: "(nat \<Rightarrow> state_key) \<Rightarrow> isabelle_rooted_context \<Rightarrow> state_rows \<Rightarrow> bool" where
  "state_presents key S R \<longleftrightarrow>
    atoms_present key (fst (snd S)) R \<and>
    rows_present key (snd S) R \<and>
    roots_present key (snd S) (fst S) R \<and>
    state_positions S\<subseteq>{..<length (fst (snd S))} \<and>
    keyed_agree row_identity (presented_rows R) (presented_rows R) \<and>
    keyed_agree row_identity (set (state_roots R)) (set (state_roots R))"

lemma state_presents_atoms: "state_presents key S R \<Longrightarrow> atoms_present key (fst (snd S)) R"
  by (simp add: state_presents_def)

lemma state_presents_rows: "state_presents key S R \<Longrightarrow> rows_present key (snd S) R"
  by (simp add: state_presents_def)

lemma state_presents_roots: "state_presents key S R \<Longrightarrow> roots_present key (snd S) (fst S) R"
  by (simp add: state_presents_def)

lemma state_presents_inside: "state_presents key S R \<Longrightarrow> state_positions S\<subseteq>{..<length (fst (snd S))}"
  by (simp add: state_presents_def)

lemma state_presents_row_keys:
  "state_presents key S R \<Longrightarrow> keyed_agree row_identity (presented_rows R) (presented_rows R)"
  by (simp add: state_presents_def)

lemma state_presents_root_keys:
  "state_presents key S R \<Longrightarrow> keyed_agree row_identity (set (state_roots R)) (set (state_roots R))"
  by (simp add: state_presents_def)

subsection \<open>Every constant an entity cites is a position of the state's table\<close>

text \<open>
  A constant an entity of a presented state declares, is a statement of, or mentions, and a constant a
  root heads, is a position of the state's table: the citation inclusions above
  (@{thm [source] entity_declared_positions}, @{thm [source] isabelle_entity_subjects_positions},
  @{thm [source] entity_mentions_positions}, @{thm [source] root_mentions_positions}) read through the
  boundary the presentation carries (@{thm [source] state_presents_inside}). The request's keys, scope and
  citations and the verdict's mentions and unreached fields consume these. Three derivations of the same
  facts from @{thm [source] state_presents_inside} are outstanding: an entity's subjects in
  @{text Development_Verdict_Statements}, an entity's positions in @{text Development_Native_Decomposition},
  and the general entity and root forms of @{text Development_Verdict_Difference}.
\<close>

lemma state_presents_declared_inside:
  assumes present: "state_presents key S R" and e: "e\<in>set (snd (snd S))"
    and d: "d\<in>set (entity_declared e)"
  shows "d<length (fst (snd S))"
  using e d entity_declared_positions state_presents_inside[OF present]
  by (force simp: state_positions_def)

lemma state_presents_subject_inside:
  assumes present: "state_presents key S R" and e: "e\<in>set (snd (snd S))"
    and d: "d\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
  shows "d<length (fst (snd S))"
  using e d isabelle_entity_subjects_positions state_presents_inside[OF present]
  by (force simp: state_positions_def)

lemma state_presents_mentions_inside:
  assumes present: "state_presents key S R" and e: "e\<in>set (snd (snd S))"
    and d: "d\<in>set (entity_mentions e)"
  shows "d<length (fst (snd S))"
  using e d entity_mentions_positions state_presents_inside[OF present]
  by (force simp: state_positions_def)

lemma state_presents_root_mentions_inside:
  assumes present: "state_presents key S R" and t: "t\<in>set (fst S)"
    and d: "d\<in>set (root_mentions t)"
  shows "d<length (fst (snd S))"
  using t d root_mentions_positions state_presents_inside[OF present]
  by (force simp: state_positions_def)

subsection \<open>A row is recovered in the family of its kind, with its citations\<close>

lemma state_presents_row:
  assumes present: "state_presents key S R" and member: "e\<in>set (snd (snd S))"
  obtains a where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
proof -
  have "set (map snd (state_entities R (entity_kind_of e)))=
      entity_row key (snd S) ` {g\<in>set (snd (snd S)). entity_kind_of g=entity_kind_of e}"
    using state_presents_rows[OF present] by (simp add: rows_present_def)
  then have "entity_row key (snd S) e\<in>set (map snd (state_entities R (entity_kind_of e)))"
    using member by auto
  then obtain a where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))" by auto
  then show ?thesis by (rule that)
qed

lemma state_presents_row_origin:
  assumes present: "state_presents key S R" and row: "(a,p)\<in>set (state_entities R k)"
  obtains e where "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
proof -
  have family: "set (map snd (state_entities R k))=
      entity_row key (snd S) ` {e\<in>set (snd (snd S)). entity_kind_of e=k}"
    using state_presents_rows[OF present] by (simp add: rows_present_def)
  have "p\<in>set (map snd (state_entities R k))" using row by force
  then obtain e where "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
    using family by auto
  then show ?thesis by (rule that)
qed

lemma entity_row_fields [simp]:
  "row_declared (entity_row key C e)=map key (entity_declared e)"
  "row_subjects (entity_row key C e)=
    map key (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"
  "row_mentions (entity_row key C e)=map key (entity_mentions e)"
  "row_identity (entity_row key C e)=isabelle_local_entities (fst C) [e]"
  by (simp_all add: entity_row_def)

lemma root_row_fields [simp]:
  "row_declared (root_row key C t)=[]"
  "row_subjects (root_row key C t)=[]"
  "row_mentions (root_row key C t)=map key (root_mentions t)"
  "row_identity (root_row key C t)=isabelle_local_root (fst C) t"
  by (simp_all add: root_row_def)

lemma state_presents_citations:
  assumes present: "state_presents key S R" and row: "(a,p)\<in>set (state_entities R k)"
  obtains e where "e\<in>set (snd (snd S))" "entity_kind_of e=k"
    "row_declared p=map key (entity_declared e)"
    "row_subjects p=map key (isabelle_entity_subjects (fst (snd S))
       (isabelle_development_constants (snd (snd S))) e)"
    "row_mentions p=map key (entity_mentions e)"
    "row_identity p=isabelle_local_entities (fst (snd S)) [e]"
proof -
  obtain e where origin: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
    by (rule state_presents_row_origin[OF present row])
  show ?thesis
  proof (rule that[of e])
    show "e\<in>set (snd (snd S))" by (rule origin(1))
    show "entity_kind_of e=k" by (rule origin(2))
    show "row_declared p=map key (entity_declared e)" by (simp add: origin(3))
    show "row_subjects p=map key (isabelle_entity_subjects (fst (snd S))
        (isabelle_development_constants (snd (snd S))) e)" by (simp add: origin(3))
    show "row_mentions p=map key (entity_mentions e)" by (simp add: origin(3))
    show "row_identity p=isabelle_local_entities (fst (snd S)) [e]" by (simp add: origin(3))
  qed
qed

text \<open>
  The entity-key condition: an entity key keys every entity's row as the presentation does. It is a
  condition of a presentation, named once here; the presenter concludes it for its own keys.
\<close>

definition entity_rows_keyed ::
    "(nat \<Rightarrow> state_key) \<Rightarrow> (isabelle_entity \<Rightarrow> state_key) \<Rightarrow> isabelle_rooted_context \<Rightarrow> state_rows \<Rightarrow> bool" where
  "entity_rows_keyed key ekey S R \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). (ekey e,entity_row key (snd S) e)\<in>presented_rows R)"

text \<open>
  Under that condition a presented row is the row of an entity of the state at that entity's key. The two
  keyed readings of a presentation's rows stand here, with the condition, and every field that reads rows
  through an entity key consumes one of them: a property of some presented row is the property of some
  entity's keyed row (@{text keyed_rows_exist}), and a property of every presented row of one entity is
  that property at its key (@{text keyed_rows_all}).
\<close>

lemma keyed_rows_exist:
  assumes present: "state_presents key S R" and keyed: "entity_rows_keyed key ekey S R"
  shows "(\<exists>z\<in>presented_rows R. Q (fst z) (snd z)) \<longleftrightarrow>
    (\<exists>e\<in>set (snd (snd S)). Q (ekey e) (entity_row key (snd S) e))"
proof
  assume "\<exists>z\<in>presented_rows R. Q (fst z) (snd z)"
  then obtain a p where z: "(a,p)\<in>presented_rows R" and q: "Q a p" by auto
  obtain j where zj: "(a,p)\<in>set (state_entities R j)" using presented_rows_family[OF z] by blast
  obtain e where e: "e\<in>set (snd (snd S))" and p: "p=entity_row key (snd S) e"
    using state_presents_row_origin[OF present zj] by metis
  have own: "(ekey e,entity_row key (snd S) e)\<in>presented_rows R" using keyed e by (simp add: entity_rows_keyed_def)
  have "a=ekey e" using keyed_agreeD[OF state_presents_row_keys[OF present] z own] p by simp
  then show "\<exists>e\<in>set (snd (snd S)). Q (ekey e) (entity_row key (snd S) e)" using e p q by blast
next
  assume "\<exists>e\<in>set (snd (snd S)). Q (ekey e) (entity_row key (snd S) e)"
  then obtain e where e: "e\<in>set (snd (snd S))" and q: "Q (ekey e) (entity_row key (snd S) e)" by blast
  have "(ekey e,entity_row key (snd S) e)\<in>presented_rows R" using keyed e by (simp add: entity_rows_keyed_def)
  then show "\<exists>z\<in>presented_rows R. Q (fst z) (snd z)" using q by force
qed

lemma keyed_rows_all:
  assumes present: "state_presents key S R" and keyed: "entity_rows_keyed key ekey S R"
    and e: "e\<in>set (snd (snd S))"
  shows "(\<forall>a. (a,entity_row key (snd S) e)\<in>presented_rows R \<longrightarrow> Q a) \<longleftrightarrow> Q (ekey e)"
proof -
  have own: "(ekey e,entity_row key (snd S) e)\<in>presented_rows R"
    using keyed e by (simp add: entity_rows_keyed_def)
  have "a=ekey e" if "(a,entity_row key (snd S) e)\<in>presented_rows R" for a
    using keyed_agreeD[OF state_presents_row_keys[OF present] that own] by simp
  then show ?thesis using own by blast
qed

subsection \<open>The keys of the atoms, and the two conditions the presentation carries\<close>

lemma atoms_present_atom:
  assumes atoms: "atoms_present key names R" and bound: "i<length names"
  shows "(key i,names!i)\<in>set (state_atoms R)"
  using atoms bound by (simp add: atoms_present_def)

lemma atoms_present_injective:
  assumes atoms: "atoms_present key names R"
  shows "inj_on (\<lambda>i. (key i,names!i)) {..<length names}"
proof -
  have image: "set (state_atoms R)=(\<lambda>i. (key i,names!i)) ` {..<length names}"
    and length: "length (state_atoms R)=length names"
    and keys: "distinct (map fst (state_atoms R))"
    using atoms by (simp_all add: atoms_present_def)
  have "distinct (state_atoms R)" using keys by (simp add: distinct_map)
  then have "card (set (state_atoms R))=length names"
    using length by (simp add: distinct_card)
  then have counted: "card ((\<lambda>i. (key i,names!i)) ` {..<length names})=card {..<length names}"
    using image by simp
  show ?thesis
    using counted inj_on_iff_eq_card[of "{..<length names}" "\<lambda>i. (key i,names!i)"] by simp
qed

theorem atoms_present_key_injective:
  assumes atoms: "atoms_present key names R"
  shows "inj_on key {..<length names}"
proof (rule inj_onI)
  fix i j assume member: "i\<in>{..<length names}" "j\<in>{..<length names}" and same: "key i=key j"
  have entries: "(key i,names!i)\<in>set (state_atoms R)" "(key j,names!j)\<in>set (state_atoms R)"
    using member by (simp_all add: atoms_present_atom[OF atoms])
  have "distinct (map fst (state_atoms R))" using atoms by (simp add: atoms_present_def)
  then have keys: "inj_on fst (set (state_atoms R))" by (simp add: distinct_map)
  have "(key i,names!i)=(key j,names!j)"
  proof (rule inj_onD[OF keys])
    show "fst (key i,names!i)=fst (key j,names!j)" using same by simp
    show "(key i,names!i)\<in>set (state_atoms R)" by (rule entries(1))
    show "(key j,names!j)\<in>set (state_atoms R)" by (rule entries(2))
  qed
  then show "i=j"
    by (rule inj_onD[OF atoms_present_injective[OF atoms] _ member(1) member(2)])
qed

text \<open>
  The verdict's ninth field, that the names of the state are distinct, is carried as a premise of
  \<open>atoms_present\<close> — a name names at most one atom — and derived here as the field, so that the
  tasks after this one consume the lemma rather than assume it. For an answer state the premise is
  established by the answer's reader, which must refuse a duplicated name.
\<close>

theorem state_presents_distinct_names:
  assumes present: "state_presents key S R"
  shows "distinct (fst (snd S))"
proof -
  let ?names="fst (snd S)"
  have atoms: "atoms_present key ?names R" by (rule state_presents_atoms[OF present])
  have "distinct (map snd (state_atoms R))" using atoms by (simp add: atoms_present_def)
  then have payloads: "inj_on snd (set (state_atoms R))" by (simp add: distinct_map)
  have apart: "?names!i\<noteq>?names!j" if bounds: "i<length ?names" "j<length ?names" and different: "i\<noteq>j"
    for i j
  proof
    assume equal: "?names!i=?names!j"
    have entries: "(key i,?names!i)\<in>set (state_atoms R)" "(key j,?names!j)\<in>set (state_atoms R)"
      using bounds by (simp_all add: atoms_present_atom[OF atoms])
    have "(key i,?names!i)=(key j,?names!j)"
    proof (rule inj_onD[OF payloads])
      show "snd (key i,?names!i)=snd (key j,?names!j)" using equal by simp
      show "(key i,?names!i)\<in>set (state_atoms R)" by (rule entries(1))
      show "(key j,?names!j)\<in>set (state_atoms R)" by (rule entries(2))
    qed
    then have "i=j"
      using bounds by (intro inj_onD[OF atoms_present_injective[OF atoms]]) simp_all
    then show False using different by simp
  qed
  show ?thesis using apart by (simp add: distinct_conv_nth)
qed

text \<open>
  A further consequence: the assessment's unknown positions are vacuous. A reference of a presented state is a
  citation of one of its atoms, and the atoms are the positions of its table, so no presented state
  has a position its table does not hold. Its owner is the presentation too.
\<close>

theorem state_presents_unknown_positions:
  assumes present: "state_presents key S R"
  shows "isabelle_unknown_positions (snd S)=[]"
proof -
  have inside: "state_positions S\<subseteq>{..<length (fst (snd S))}" by (rule state_presents_inside[OF present])
  have "\<forall>i\<in>set (concat (map isabelle_entity_positions (snd (snd S)))). isabelle_name_at (fst (snd S)) i\<noteq>None"
  proof
    fix i assume "i\<in>set (concat (map isabelle_entity_positions (snd (snd S))))"
    then have "i\<in>state_positions S" by (auto simp: state_positions_def)
    then have "i<length (fst (snd S))" using inside by auto
    then show "isabelle_name_at (fst (snd S)) i\<noteq>None" by (simp add: isabelle_name_at_def)
  qed
  then show ?thesis by (simp add: isabelle_unknown_positions_def filter_empty_conv)
qed

subsection \<open>No reference lies outside the state's atoms\<close>

lemma state_presents_cited_key:
  assumes present: "state_presents key S R" and member: "i\<in>state_positions S"
  shows "key i\<in>fst ` set (state_atoms R)"
proof -
  have "i<length (fst (snd S))" using member state_presents_inside[OF present] by auto
  then have "(key i,fst (snd S)!i)\<in>set (state_atoms R)"
    by (simp add: atoms_present_atom[OF state_presents_atoms[OF present]])
  then show ?thesis by force
qed

theorem state_presents_cited_atoms:
  assumes present: "state_presents key S R" and row: "(a,p)\<in>set (state_entities R k)"
  shows "set (row_declared p)\<union>set (row_subjects p)\<union>set (row_mentions p)\<subseteq>fst ` set (state_atoms R)"
proof -
  obtain e where member: "e\<in>set (snd (snd S))" and origin: "p=entity_row key (snd S) e"
    by (rule state_presents_row_origin[OF present row])
  have positions: "set (isabelle_entity_positions e)\<subseteq>state_positions S"
    using member by (auto simp: state_positions_def)
  have declared: "set (entity_declared e)\<subseteq>state_positions S"
    using entity_declared_positions[of e] positions by auto
  have subjects: "set (isabelle_entity_subjects (fst (snd S))
      (isabelle_development_constants (snd (snd S))) e)\<subseteq>state_positions S"
    using isabelle_entity_subjects_positions[of "fst (snd S)"
      "isabelle_development_constants (snd (snd S))" e] positions by auto
  have mentions: "set (entity_mentions e)\<subseteq>state_positions S"
    using entity_mentions_positions[of e] positions by auto
  show ?thesis
    using declared subjects mentions state_presents_cited_key[OF present]
    by (auto simp: origin)
qed

theorem state_presents_root_cited_atoms:
  assumes present: "state_presents key S R" and root: "(a,p)\<in>set (state_roots R)"
  shows "set (row_mentions p)\<subseteq>fst ` set (state_atoms R)"
proof -
  have roots: "map snd (state_roots R)=map (root_row key (snd S)) (fst S)"
    using state_presents_roots[OF present] by (simp add: roots_present_def)
  have "p\<in>set (map snd (state_roots R))" using root by force
  then obtain t where member: "t\<in>set (fst S)" and origin: "p=root_row key (snd S) t"
    using roots by auto
  have positions: "set (isabelle_term_positions t)\<subseteq>state_positions S"
    using member by (auto simp: state_positions_def)
  have mentions: "set (root_mentions t)\<subseteq>state_positions S"
    using root_mentions_positions[of t] positions by auto
  show ?thesis
    using mentions state_presents_cited_key[OF present] by (auto simp: origin)
qed

subsection \<open>The roots are a family, in their own order\<close>

lemma state_presents_root_family:
  assumes present: "state_presents key S R"
  shows "map snd (state_roots R)=map (root_row key (snd S)) (fst S)"
  using state_presents_roots[OF present] by (simp add: roots_present_def)

lemma state_presents_root_length:
  assumes present: "state_presents key S R"
  shows "length (state_roots R)=length (fst S)"
  using state_presents_root_family[OF present] by (metis length_map)

lemma state_presents_root_row:
  assumes present: "state_presents key S R" and bound: "i<length (fst S)"
  shows "snd (state_roots R!i)=root_row key (snd S) (fst S!i)"
proof -
  have length: "length (state_roots R)=length (fst S)" by (rule state_presents_root_length[OF present])
  have "snd (state_roots R!i)=map snd (state_roots R)!i" using bound length by simp
  also have "\<dots>=map (root_row key (snd S)) (fst S)!i"
    by (simp only: state_presents_root_family[OF present])
  also have "\<dots>=root_row key (snd S) (fst S!i)" using bound by simp
  finally show ?thesis .
qed

text \<open>
  A further condition the presentation carries: the root family's keys are distinct and each root
  agrees with itself by identity, so two positions of the roots with one local presentation would
  have one key. The roots are therefore distinct as local presentations. Its owner is the exporter
  that defines the state's roots; an answer state is exported from the same roots.
\<close>

lemma state_presents_distinct_roots:
  assumes present: "state_presents key S R"
  shows "distinct (map (isabelle_local_root (fst (snd S))) (fst S))"
proof (subst distinct_conv_nth, intro allI impI)
  fix i j
  assume i: "i<length (map (isabelle_local_root (fst (snd S))) (fst S))"
    and j: "j<length (map (isabelle_local_root (fst (snd S))) (fst S))" and ne: "i\<noteq>j"
  have bi: "i<length (fst S)" using i by simp
  have bj: "j<length (fst S)" using j by simp
  have length: "length (state_roots R)=length (fst S)" by (rule state_presents_root_length[OF present])
  show "map (isabelle_local_root (fst (snd S))) (fst S)!i\<noteq>map (isabelle_local_root (fst (snd S))) (fst S)!j"
  proof
    assume same: "map (isabelle_local_root (fst (snd S))) (fst S)!i=map (isabelle_local_root (fst (snd S))) (fst S)!j"
    have ids: "row_identity (snd (state_roots R!i))=row_identity (snd (state_roots R!j))"
      using same bi bj by (simp only: state_presents_root_row[OF present bi]
        state_presents_root_row[OF present bj] root_row_fields nth_map)
    have mi: "(fst (state_roots R!i),snd (state_roots R!i))\<in>set (state_roots R)" using bi length by simp
    have mj: "(fst (state_roots R!j),snd (state_roots R!j))\<in>set (state_roots R)" using bj length by simp
    have "(fst (state_roots R!i)=fst (state_roots R!j))=
        (row_identity (snd (state_roots R!i))=row_identity (snd (state_roots R!j)))"
      by (rule keyed_agreeD[OF state_presents_root_keys[OF present] mi mj])
    then have keys: "fst (state_roots R!i)=fst (state_roots R!j)" using ids by simp
    have distinct: "distinct (map fst (state_roots R))"
      using state_presents_roots[OF present] by (simp add: roots_present_def)
    have "(map fst (state_roots R)!i=map fst (state_roots R)!j)=(i=j)"
      by (rule nth_eq_iff_index_eq[OF distinct]) (simp_all add: bi bj length)
    then show False using keys bi bj length ne by simp
  qed
qed

subsection \<open>A row belongs to exactly one family\<close>

text \<open>
  Every kind of the entity language has its family, and the families of two kinds share no row: the
  identity a row carries is the local presentation of its own entity, and a local presentation is
  the entity itself with its names, so two rows of one identity are rows of entities of one kind.
  No relation reads that identity to tell a kind; this is a property of the presentation, and the
  families remain what tells a kind apart.
\<close>

lemma isabelle_local_entities_kind:
  assumes same: "isabelle_local_entities names [e]=isabelle_local_entities names' [g]"
  shows "entity_kind_of e=entity_kind_of g"
proof -
  have "isabelle_entity_rename (isabelle_local_embedding names (isabelle_entity_positions e)) e=
      isabelle_entity_rename (isabelle_local_embedding names' (isabelle_entity_positions g)) g"
    using same by (simp add: isabelle_local_entities_def Let_def)
  then have "entity_kind_of
      (isabelle_entity_rename (isabelle_local_embedding names (isabelle_entity_positions e)) e)=
    entity_kind_of
      (isabelle_entity_rename (isabelle_local_embedding names' (isabelle_entity_positions g)) g)"
    by (rule arg_cong)
  then show ?thesis by simp
qed

theorem state_presents_families_disjoint:
  assumes present: "state_presents key S R" and different: "k\<noteq>k'"
  shows "set (map snd (state_entities R k))\<inter>set (map snd (state_entities R k'))={}"
proof (rule equals0I)
  fix p assume member: "p\<in>set (map snd (state_entities R k))\<inter>set (map snd (state_entities R k'))"
  then obtain a b where rows: "(a,p)\<in>set (state_entities R k)" "(b,p)\<in>set (state_entities R k')"
    by auto
  obtain e where left: "entity_kind_of e=k" "p=entity_row key (snd S) e"
    by (rule state_presents_row_origin[OF present rows(1)])
  obtain g where right: "entity_kind_of g=k'" "p=entity_row key (snd S) g"
    by (rule state_presents_row_origin[OF present rows(2)])
  have "row_identity (entity_row key (snd S) e)=row_identity (entity_row key (snd S) g)"
    using left(2) right(2) by simp
  then have "isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S)) [g]"
    by simp
  then have "entity_kind_of e=entity_kind_of g" by (rule isabelle_local_entities_kind)
  then show False using left(1) right(1) different by simp
qed

theorem state_presents_kind_family:
  assumes present: "state_presents key S R" and member: "e\<in>set (snd (snd S))"
  shows "entity_row key (snd S) e\<in>set (map snd (state_entities R (entity_kind_of e)))"
proof -
  obtain a where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
    by (rule state_presents_row[OF present member])
  then show ?thesis by force
qed

theorem state_presents_kind_only:
  assumes present: "state_presents key S R" and member: "e\<in>set (snd (snd S))"
    and different: "k\<noteq>entity_kind_of e"
  shows "entity_row key (snd S) e\<notin>set (map snd (state_entities R k))"
  using state_presents_kind_family[OF present member]
    state_presents_families_disjoint[OF present different] by auto

subsection \<open>A kind predicate is a selection of families\<close>

text \<open>
  The verdict's two kind arguments — what an answer may replace and what it must state — are kind
  predicates on the source side. Each is a selection of families here, and the rows of the selected
  families are exactly the rows of the entities the predicate holds of. This is what keeps the
  refinement and the definition verdicts instances of one definition at their selections.
\<close>

definition kinds_present :: "(isabelle_entity \<Rightarrow> bool) \<Rightarrow> entity_kind set \<Rightarrow> bool" where
  "kinds_present P ks \<longleftrightarrow> (\<forall>e. P e=(entity_kind_of e\<in>ks))"

lemma kinds_presentD: "kinds_present P ks \<Longrightarrow> P e=(entity_kind_of e\<in>ks)"
  by (simp add: kinds_present_def)

theorem kinds_present_rows:
  assumes present: "state_presents key S R" and kinds: "kinds_present P ks"
  shows "(\<Union>k\<in>ks. set (map snd (state_entities R k)))=
    entity_row key (snd S) ` {e\<in>set (snd (snd S)). P e}"
proof
  show "(\<Union>k\<in>ks. set (map snd (state_entities R k)))\<subseteq>
      entity_row key (snd S) ` {e\<in>set (snd (snd S)). P e}"
  proof
    fix p assume "p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k)))"
    then obtain k where selected: "k\<in>ks" and member: "p\<in>set (map snd (state_entities R k))" by auto
    then obtain a where "(a,p)\<in>set (state_entities R k)" by auto
    then obtain e where origin: "e\<in>set (snd (snd S))" "entity_kind_of e=k" "p=entity_row key (snd S) e"
      by (rule state_presents_row_origin[OF present])
    have "P e" using origin selected by (simp add: kinds_presentD[OF kinds])
    then show "p\<in>entity_row key (snd S) ` {e\<in>set (snd (snd S)). P e}" using origin by auto
  qed
next
  show "entity_row key (snd S) ` {e\<in>set (snd (snd S)). P e}\<subseteq>
      (\<Union>k\<in>ks. set (map snd (state_entities R k)))"
  proof
    fix p assume "p\<in>entity_row key (snd S) ` {e\<in>set (snd (snd S)). P e}"
    then obtain e where member: "e\<in>set (snd (snd S))" and holds: "P e"
      and origin: "p=entity_row key (snd S) e" by auto
    have selected: "entity_kind_of e\<in>ks" using holds by (simp add: kinds_presentD[OF kinds])
    have "p\<in>set (map snd (state_entities R (entity_kind_of e)))"
      using origin state_presents_kind_family[OF present member] by simp
    then show "p\<in>(\<Union>k\<in>ks. set (map snd (state_entities R k)))" using selected by auto
  qed
qed

subsection \<open>Two states over one set of atoms\<close>

text \<open>
  Two presented states share their keys when a key of the one and a key of the other are equal
  exactly if they key the same name, or the same identity. Then a row of one state and a row of the
  other are compared by their keys alone, and the correspondence of the two name tables never
  appears in a program: it appears only here, where the shared keys are related back to it.
\<close>

definition keys_shared :: "state_rows \<Rightarrow> state_rows \<Rightarrow> bool" where
  "keys_shared R R' \<longleftrightarrow>
    keyed_agree id (set (state_atoms R)) (set (state_atoms R')) \<and>
    keyed_agree row_identity (presented_rows R) (presented_rows R') \<and>
    keyed_agree row_identity (set (state_roots R)) (set (state_roots R'))"

lemma keys_shared_atoms: "keys_shared R R' \<Longrightarrow> keyed_agree id (set (state_atoms R)) (set (state_atoms R'))"
  by (simp add: keys_shared_def)

lemma keys_shared_rows:
  "keys_shared R R' \<Longrightarrow> keyed_agree row_identity (presented_rows R) (presented_rows R')"
  by (simp add: keys_shared_def)

lemma keys_shared_roots:
  "keys_shared R R' \<Longrightarrow> keyed_agree row_identity (set (state_roots R)) (set (state_roots R'))"
  by (simp add: keys_shared_def)

theorem keys_shared_atom:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and bound: "i<length (fst (snd S))" and bound': "j<length (fst (snd S'))"
  shows "(key i=key' j)=(fst (snd S)!i=fst (snd S')!j)"
proof -
  have left: "(key i,fst (snd S)!i)\<in>set (state_atoms R)"
    using bound by (simp add: atoms_present_atom[OF state_presents_atoms[OF present]])
  have right: "(key' j,fst (snd S')!j)\<in>set (state_atoms R')"
    using bound' by (simp add: atoms_present_atom[OF state_presents_atoms[OF present']])
  show ?thesis
    using keyed_agreeD[OF keys_shared_atoms[OF shared] left right] by simp
qed

theorem keys_shared_embedding:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and bound: "i<length (fst (snd S))"
    and named: "fst (snd S)!i\<in>set (fst (snd S'))"
  shows "key' (isabelle_state_embedding (fst (snd S)) (fst (snd S')) i)=key i"
proof -
  let ?names="fst (snd S)" and ?names'="fst (snd S')"
  obtain j where found: "isabelle_name_position ?names' (?names!i)=Some j"
    using named isabelle_name_position_none[of ?names' "?names!i"]
    by (cases "isabelle_name_position ?names' (?names!i)") auto
  have at: "j<length ?names'\<and>?names'!j=?names!i" by (rule isabelle_name_position_some[OF found])
  have embedding: "isabelle_state_embedding ?names ?names' i=j"
    using bound found by (simp add: isabelle_state_embedding_def isabelle_name_at_def)
  have "(key i=key' j)=(?names!i=?names'!j)"
    by (rule keys_shared_atom[OF present present' shared bound]) (simp add: at)
  then show ?thesis using at embedding by simp
qed

theorem keys_shared_row:
  assumes shared: "keys_shared R R'"
    and row: "(a,p)\<in>presented_rows R" and row': "(b,q)\<in>presented_rows R'"
  shows "(a=b)=(row_identity p=row_identity q)"
  by (rule keyed_agreeD[OF keys_shared_rows[OF shared] row row'])

theorem keys_shared_entity:
  assumes present: "state_presents key S R" and present': "state_presents key' S' R'"
    and shared: "keys_shared R R'"
    and member: "e\<in>set (snd (snd S))" and member': "g\<in>set (snd (snd S'))"
  obtains a b where "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
    and "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))"
    and "(a=b)=(isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S')) [g])"
proof -
  obtain a where left: "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))"
    by (rule state_presents_row[OF present member])
  obtain b where right: "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))"
    by (rule state_presents_row[OF present' member'])
  have keys: "(a=b)=(row_identity (entity_row key (snd S) e)=row_identity (entity_row key' (snd S') g))"
    by (rule keys_shared_row[OF shared presented_rows_member[OF left] presented_rows_member[OF right]])
  show ?thesis
  proof (rule that[of a b])
    show "(a,entity_row key (snd S) e)\<in>set (state_entities R (entity_kind_of e))" by (rule left)
    show "(b,entity_row key' (snd S') g)\<in>set (state_entities R' (entity_kind_of g))" by (rule right)
    show "(a=b)=(isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S')) [g])"
      using keys by simp
  qed
qed

subsection \<open>A correspondence of tables carries a presentation\<close>

text \<open>
  A state and its renaming under a correspondence of name tables have the same presentation, once
  the keys of the moved positions are the keys of the original ones. Every row is unchanged: its
  citations move with the correspondence and its identity is invariant, which is
  \<open>isabelle_local_entities_renamed\<close> and its consequence for roots, consumed here. This is why no
  program of the verdict mentions a correspondence.
\<close>

lemma entity_row_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and keys: "\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> key' (f i)=key i"
    and inside: "\<And>i. i\<in>set (isabelle_entity_positions e) \<Longrightarrow> i<length names"
  shows "entity_row key' (names',map (isabelle_entity_rename f) es) (isabelle_entity_rename f e)=
    entity_row key (names,es) e"
proof -
  have declared: "map key' (entity_declared (isabelle_entity_rename f e))=map key (entity_declared e)"
    using keys entity_declared_positions[of e]
    by (auto simp: entity_declared_def isabelle_entity_rename_declared split: option.splits)
  have subjects: "map key' (isabelle_entity_subjects names'
      (isabelle_development_constants (map (isabelle_entity_rename f) es)) (isabelle_entity_rename f e))=
    map key (isabelle_entity_subjects names (isabelle_development_constants es) e)"
    using keys isabelle_entity_subjects_positions[of names "isabelle_development_constants es" e]
    by (simp add: isabelle_rename_development_constants isabelle_rename_entity_subjects[OF corr] subset_iff)
  have mentions: "map key' (entity_mentions (isabelle_entity_rename f e))=map key (entity_mentions e)"
    using keys entity_mentions_positions[of e]
    by (auto simp: entity_mentions_def isabelle_entity_rename_specified isabelle_term_rename_constants
      split: option.splits)
  have identity: "isabelle_local_entities names' [isabelle_entity_rename f e]=
      isabelle_local_entities names [e]"
    using isabelle_local_entities_renamed[OF corr, of "[e]"] inside by simp
  show ?thesis by (simp add: entity_row_def declared subjects mentions identity)
qed

lemma root_row_renamed:
  assumes corr: "isabelle_table_correspondence f names names'"
    and keys: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> key' (f i)=key i"
    and inside: "\<And>i. i\<in>set (isabelle_term_positions t) \<Longrightarrow> i<length names"
  shows "root_row key' (names',es') (isabelle_term_rename f t)=root_row key (names,es) t"
proof -
  have mentions: "map key' (root_mentions (isabelle_term_rename f t))=map key (root_mentions t)"
    using keys root_mentions_positions[of t]
    by (auto simp: root_mentions_def isabelle_term_rename_head split: option.splits)
  show ?thesis
    by (simp add: root_row_def mentions isabelle_local_root_renamed[OF corr inside])
qed

theorem state_presents_renamed:
  assumes corr: "isabelle_table_correspondence f (fst (snd S)) names'"
    and length: "length names'=length (fst (snd S))"
    and keys: "\<And>i. i<length (fst (snd S)) \<Longrightarrow> key' (f i)=key i"
    and present: "state_presents key S R"
  shows "state_presents key' (map (isabelle_term_rename f) (fst S),
    names',map (isabelle_entity_rename f) (snd (snd S))) R"
proof -
  let ?names="fst (snd S)" and ?es="snd (snd S)" and ?roots="fst S"
  let ?T="(map (isabelle_term_rename f) ?roots,names',map (isabelle_entity_rename f) ?es)"
  have inside: "i<length ?names" if "i\<in>state_positions S" for i
    using that state_presents_inside[OF present] by auto
  have entity_inside: "i<length ?names" if member: "e\<in>set ?es"
    and position: "i\<in>set (isabelle_entity_positions e)" for e i
  proof -
    have "i\<in>state_positions S" using member position by (simp add: state_positions_def) blast
    then show ?thesis by (rule inside)
  qed
  have root_inside: "i<length ?names" if member: "t\<in>set ?roots"
    and position: "i\<in>set (isabelle_term_positions t)" for t i
  proof -
    have "i\<in>state_positions S" using member position by (simp add: state_positions_def) blast
    then show ?thesis by (rule inside)
  qed
  have moved: "f i<length names'\<and>names'!(f i)=?names!i" if bound: "i<length ?names" for i
  proof -
    have "isabelle_name_at names' (f i)=isabelle_name_at ?names i"
      by (rule isabelle_table_correspondence_name[OF corr])
    then have "isabelle_name_at names' (f i)=Some (?names!i)"
      using bound by (simp add: isabelle_name_at_def)
    then show ?thesis by (simp add: isabelle_name_at_def split: if_splits)
  qed
  have onto: "f ` {..<length ?names}={..<length names'}"
  proof (rule card_seteq)
    show "finite {..<length names'}" by simp
    show "f ` {..<length ?names}\<subseteq>{..<length names'}"
    proof
      fix j assume "j\<in>f ` {..<length ?names}"
      then obtain i where bound: "i<length ?names" and image: "j=f i" by auto
      show "j\<in>{..<length names'}" using image moved[OF bound] by simp
    qed
    have "inj_on f {..<length ?names}"
      by (rule inj_on_subset[OF isabelle_table_correspondence_injective[OF corr] subset_UNIV])
    then have "card (f ` {..<length ?names})=length ?names" by (simp add: card_image)
    then show "card {..<length names'}\<le>card (f ` {..<length ?names})" using length by simp
  qed
  have atoms: "atoms_present key' names' R"
  proof -
    have old: "set (state_atoms R)=(\<lambda>i. (key i,?names!i)) ` {..<length ?names}"
      and count: "length (state_atoms R)=length ?names"
      and keyed: "distinct (map fst (state_atoms R))"
      and payloads: "distinct (map snd (state_atoms R))"
      using state_presents_atoms[OF present] by (simp_all add: atoms_present_def)
    have pointwise: "(key' (f i),names'!(f i))=(key i,?names!i)" if bound: "i<length ?names" for i
      using keys[OF bound] moved[OF bound] by simp
    have "(\<lambda>j. (key' j,names'!j)) ` {..<length names'}=
        (\<lambda>j. (key' j,names'!j)) ` (f ` {..<length ?names})" by (simp only: onto)
    also have "\<dots>=(\<lambda>i. (key' (f i),names'!(f i))) ` {..<length ?names}"
      by (simp add: image_image)
    also have "\<dots>=(\<lambda>i. (key i,?names!i)) ` {..<length ?names}"
      by (rule image_cong[OF refl]) (simp add: pointwise)
    finally have "set (state_atoms R)=(\<lambda>j. (key' j,names'!j)) ` {..<length names'}"
      by (simp only: old)
    then show ?thesis using count keyed payloads length by (simp add: atoms_present_def)
  qed
  have rows: "rows_present key' (snd ?T) R"
  proof -
    have row: "entity_row key' (names',map (isabelle_entity_rename f) ?es) (isabelle_entity_rename f e)=
        entity_row key (?names,?es) e" if member: "e\<in>set ?es" for e
    proof (rule entity_row_renamed[OF corr])
      fix i assume "i\<in>set (isabelle_entity_positions e)"
      then have "i<length ?names" by (rule entity_inside[OF member])
      then show "key' (f i)=key i" by (rule keys)
    next
      fix i assume "i\<in>set (isabelle_entity_positions e)"
      then show "i<length ?names" by (rule entity_inside[OF member])
    qed
    have family: "set (map snd (state_entities R k))=
        entity_row key' (snd ?T) ` {g\<in>set (map (isabelle_entity_rename f) ?es). entity_kind_of g=k}" for k
    proof -
      have selected: "{g\<in>set (map (isabelle_entity_rename f) ?es). entity_kind_of g=k}=
          isabelle_entity_rename f ` {e\<in>set ?es. entity_kind_of e=k}" by auto
      have "entity_row key' (snd ?T) ` (isabelle_entity_rename f ` {e\<in>set ?es. entity_kind_of e=k})=
          (\<lambda>e. entity_row key' (snd ?T) (isabelle_entity_rename f e)) ` {e\<in>set ?es. entity_kind_of e=k}"
        by (simp add: image_image)
      also have "\<dots>=entity_row key (snd S) ` {e\<in>set ?es. entity_kind_of e=k}"
        by (rule image_cong[OF refl]) (simp add: row)
      finally have image: "entity_row key' (snd ?T) `
          {g\<in>set (map (isabelle_entity_rename f) ?es). entity_kind_of g=k}=
        entity_row key (snd S) ` {e\<in>set ?es. entity_kind_of e=k}" by (simp only: selected)
      show ?thesis
        using state_presents_rows[OF present] by (simp only: image rows_present_def)
    qed
    show ?thesis using family state_presents_rows[OF present] by (simp add: rows_present_def)
  qed
  have roots: "roots_present key' (snd ?T) (fst ?T) R"
  proof -
    have row: "root_row key' (names',map (isabelle_entity_rename f) ?es) (isabelle_term_rename f t)=
        root_row key (?names,?es) t" if member: "t\<in>set ?roots" for t
    proof (rule root_row_renamed[OF corr])
      fix i assume "i\<in>set (isabelle_term_positions t)"
      then have "i<length ?names" by (rule root_inside[OF member])
      then show "key' (f i)=key i" by (rule keys)
    next
      fix i assume "i\<in>set (isabelle_term_positions t)"
      then show "i<length ?names" by (rule root_inside[OF member])
    qed
    have "map (root_row key' (snd ?T)) (map (isabelle_term_rename f) ?roots)=
        map (\<lambda>t. root_row key' (snd ?T) (isabelle_term_rename f t)) ?roots" by simp
    also have "\<dots>=map (root_row key (snd S)) ?roots"
      by (rule map_cong[OF refl]) (simp add: row)
    also have "\<dots>=map snd (state_roots R)" by (rule state_presents_root_family[OF present, symmetric])
    finally have "map snd (state_roots R)=map (root_row key' (snd ?T)) (fst ?T)" by simp
    then show ?thesis using state_presents_roots[OF present] by (simp add: roots_present_def)
  qed
  have positions: "state_positions ?T\<subseteq>{..<length names'}"
  proof
    fix j assume "j\<in>state_positions ?T"
    then consider (entity) g where "g\<in>set ?es" "j\<in>set (isabelle_entity_positions (isabelle_entity_rename f g))"
      | (root) t where "t\<in>set ?roots" "j\<in>set (isabelle_term_positions (isabelle_term_rename f t))"
      by (auto simp: state_positions_def)
    then show "j\<in>{..<length names'}"
    proof cases
      case (entity g)
      then obtain i where position: "i\<in>set (isabelle_entity_positions g)" and image: "j=f i"
        by (auto simp: isabelle_entity_rename_positions)
      have bound: "i<length ?names" by (rule entity_inside[OF entity(1) position])
      show ?thesis using image moved[OF bound] by simp
    next
      case (root t)
      then obtain i where position: "i\<in>set (isabelle_term_positions t)" and image: "j=f i"
        by (auto simp: isabelle_term_rename_positions)
      have bound: "i<length ?names" by (rule root_inside[OF root(1) position])
      show ?thesis using image moved[OF bound] by simp
    qed
  qed
  show ?thesis
    using atoms rows roots positions state_presents_row_keys[OF present]
      state_presents_root_keys[OF present]
    by (simp add: state_presents_def)
qed

end
