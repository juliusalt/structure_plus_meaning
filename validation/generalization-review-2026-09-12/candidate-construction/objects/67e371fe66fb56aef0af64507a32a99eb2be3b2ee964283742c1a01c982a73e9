theory Factor_Construction
  imports RRA_Assembly
begin

section \<open>Declared occurrences and separately supplied base sources\<close>

fun construction_source_at ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    nat + 'b \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "construction_source_at xs B (Inl i) R \<longleftrightarrow> i < length xs \<and> R = xs ! i"
| "construction_source_at xs B (Inr b) R \<longleftrightarrow> (b,R) \<in> B"

fun construction_source_value ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    nat + 'b \<Rightarrow> exact_artifact" where
  "construction_source_value xs B (Inl i) = xs ! i"
| "construction_source_value xs B (Inr b) = rel_value B b"

definition construction_sources_formed ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow> bool" where
  "construction_sources_formed xs B \<longleftrightarrow>
    (\<forall>R\<in>set xs. exact_formed R) \<and> finite B \<and> single_valued B \<and>
    (\<forall>b R. (b,R) \<in> B \<longrightarrow> exact_formed R)"

lemma construction_source_value_at:
  assumes sf: "construction_sources_formed xs B"
    and source: "construction_source_at xs B j R"
  shows "construction_source_value xs B j = R" "exact_formed R"
proof -
  show "construction_source_value xs B j = R"
  proof (cases j)
    case (Inl i)
    then show ?thesis using source by simp
  next
    case (Inr b)
    have sv: "single_valued B" using sf by (simp add: construction_sources_formed_def)
    have member: "(b,R) \<in> B" using source Inr by simp
    show ?thesis using Inr rel_value_eq[OF sv member] by simp
  qed
  show "exact_formed R"
    using sf source by (cases j) (auto simp: construction_sources_formed_def)
qed

definition construction_fragment ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    nat + 'b \<Rightarrow> local_address set \<Rightarrow> exact_fragment" where
  "construction_fragment xs B j A =
    \<lparr>fragment_source = construction_source_value xs B j,
     fragment_selection = A\<rparr>"

definition source_selection_valid ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    nat + 'b \<Rightarrow> local_address set \<Rightarrow> bool" where
  "source_selection_valid xs B j A \<longleftrightarrow>
    (\<exists>R. construction_source_at xs B j R) \<and> finite A \<and>
    A \<subseteq> rra_carrier (object_structure (construction_source_value xs B j))"

lemma selected_fragment_formed:
  assumes sf: "construction_sources_formed xs B" and valid: "source_selection_valid xs B j A"
  shows "fragment_formed (construction_fragment xs B j A)"
proof -
  obtain R where source: "construction_source_at xs B j R"
    using valid by (auto simp: source_selection_valid_def)
  have resolved: "construction_source_value xs B j = R" and rf: "exact_formed R"
    using construction_source_value_at[OF sf source] by auto
  show ?thesis using valid resolved rf
    by (simp add: source_selection_valid_def construction_fragment_def fragment_formed_def)
qed

text \<open>
  The two source classes are separate inputs to this relation. Positions in xs
  preserve order and repetition; a base key never denotes an input position.
  Supplying B records an admitted base boundary. It does not prove that any
  particular program permits that boundary. That further semantic judgment
  must include these exact inputs.
\<close>

section \<open>One source selection for each assembly piece\<close>

record ('b,'s) source_construction =
  construction_selections :: "('s \<times> ((nat + 'b) \<times> local_address set)) set"
  construction_origins :: "(('s \<times> local_address) \<times> local_address) set"

definition construction_selection_formed ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> bool" where
  "construction_selection_formed xs B W \<longleftrightarrow>
    construction_sources_formed xs B \<and>
    finite (construction_selections W) \<and> single_valued (construction_selections W) \<and>
    (\<forall>s j A. (s,j,A) \<in> construction_selections W \<longrightarrow>
      source_selection_valid xs B j A)"

definition construction_pieces ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> 's exact_piece_family" where
  "construction_pieces xs B W =
    \<lparr>piece_graph = map_prod id
      (\<lambda>(j,A). fragment_material (construction_fragment xs B j A)) `
        construction_selections W\<rparr>"

definition construction_assembly ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> 's assembly_witness" where
  "construction_assembly xs B W =
    \<lparr>assembly_pieces = construction_pieces xs B W,
     assembly_origin = construction_origins W\<rparr>"

definition source_constructs ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> exact_artifact \<Rightarrow> bool" where
  "source_constructs xs B W R \<longleftrightarrow>
    construction_selection_formed xs B W \<and>
    assembly_relation (construction_pieces xs B W) (construction_origins W) R"

lemma construction_piece_member:
  "(s,R) \<in> piece_graph (construction_pieces xs B W) \<longleftrightarrow>
    (\<exists>j A. (s,j,A) \<in> construction_selections W \<and>
      R = fragment_material (construction_fragment xs B j A))"
proof
  assume member: "(s,R) \<in> piece_graph (construction_pieces xs B W)"
  obtain z where z: "z \<in> construction_selections W"
    "(s,R) = map_prod id (\<lambda>(j,A). fragment_material (construction_fragment xs B j A)) z"
    using member by (auto simp: construction_pieces_def)
  obtain k v where outer: "z = (k,v)" by (cases z) auto
  obtain j A where inner: "v = (j,A)" by (cases v) auto
  have same: "k=s" "R = fragment_material (construction_fragment xs B j A)"
    using z(2) outer inner by simp_all
  show "\<exists>j A. (s,j,A) \<in> construction_selections W \<and>
    R = fragment_material (construction_fragment xs B j A)"
    by (rule exI[of _ j], rule exI[of _ A]) (use z(1) outer inner same in simp)
next
  assume "\<exists>j A. (s,j,A) \<in> construction_selections W \<and>
    R = fragment_material (construction_fragment xs B j A)"
  then obtain j A where choice: "(s,j,A) \<in> construction_selections W"
    "R = fragment_material (construction_fragment xs B j A)" by blast
  have "(s,fragment_material (construction_fragment xs B j A)) \<in>
    map_prod id (\<lambda>(j,A). fragment_material (construction_fragment xs B j A)) `
      construction_selections W"
    by (rule rev_image_eqI[OF choice(1)]) simp
  then show "(s,R) \<in> piece_graph (construction_pieces xs B W)"
    using choice(2) by (simp add: construction_pieces_def)
qed

lemma construction_piece_slots:
  "piece_slots (construction_pieces xs B W) = rel_dom (construction_selections W)"
  by (auto simp: piece_slots_def rel_dom_def construction_piece_member)

lemma construction_pieces_formed:
  assumes formed: "construction_selection_formed xs B W"
  shows "piece_family_formed (construction_pieces xs B W)"
proof -
  have sf: "construction_sources_formed xs B"
    and fin: "finite (construction_selections W)"
    and sv: "single_valued (construction_selections W)"
    and sel: "\<And>s j A. (s,j,A) \<in> construction_selections W \<Longrightarrow>
      source_selection_valid xs B j A"
    using formed by (auto simp: construction_selection_formed_def)
  have psv: "single_valued (piece_graph (construction_pieces xs B W))"
    using sv by (auto simp: single_valued_def construction_piece_member; blast)
  have pf: "\<And>s R. (s,R) \<in> piece_graph (construction_pieces xs B W) \<Longrightarrow>
    exact_formed R"
    using fragment_material_formed[OF selected_fragment_formed[OF sf sel]]
    by (auto simp: construction_piece_member)
  show ?thesis using fin psv pf
    by (auto simp: piece_family_formed_def construction_pieces_def)
qed

theorem source_constructs_iff_K2:
  "source_constructs xs B W R \<longleftrightarrow>
    construction_selection_formed xs B W \<and>
    K2 (construction_assembly xs B W) \<and>
    R = assembly_output (construction_assembly xs B W)"
  unfolding source_constructs_def
  using assembly_relation_iff[of "construction_assembly xs B W" R]
  by (simp add: construction_assembly_def)

lemma source_construction_finite:
  assumes "source_constructs xs B W R"
  shows "finite B" "single_valued B"
    "finite (construction_selections W)" "single_valued (construction_selections W)"
    "finite (construction_origins W)" "single_valued (construction_origins W)"
    "exact_formed R"
  using assms
  by (auto simp: source_constructs_def construction_selection_formed_def
    construction_sources_formed_def assembly_relation_def exact_map_def)

lemma construction_has_no_unexplained_piece:
  assumes "source_constructs xs B W R"
    "(s,T) \<in> piece_graph (construction_pieces xs B W)"
  shows "\<exists>j A S. (s,j,A) \<in> construction_selections W \<and>
    construction_source_at xs B j S \<and>
    fragment_formed \<lparr>fragment_source = S, fragment_selection = A\<rparr> \<and>
    T = restrict_object S A"
proof -
  obtain j A where choice: "(s,j,A) \<in> construction_selections W"
    "T = fragment_material (construction_fragment xs B j A)"
    using assms(2) by (simp add: construction_piece_member) blast
  have sf: "construction_sources_formed xs B" and sel: "source_selection_valid xs B j A"
    using assms(1) choice(1)
    by (auto simp: source_constructs_def construction_selection_formed_def)
  obtain S where source: "construction_source_at xs B j S"
    using sel by (auto simp: source_selection_valid_def)
  have resolved: "construction_source_value xs B j = S"
    by (rule construction_source_value_at(1)[OF sf source])
  have ff: "fragment_formed \<lparr>fragment_source = S, fragment_selection = A\<rparr>"
    using selected_fragment_formed[OF sf sel] resolved by (simp add: construction_fragment_def)
  show ?thesis using choice source ff resolved
    by (auto simp: construction_fragment_def fragment_material_def)
qed

theorem construction_output_atom_origin:
  assumes built: "source_constructs xs B W R"
    and atom: "a \<in> rra_carrier (object_structure R)"
  shows "\<exists>s j A S x. (s,j,A) \<in> construction_selections W \<and>
    construction_source_at xs B j S \<and> x \<in> A \<and>
    x \<in> rra_carrier (object_structure S) \<and>
    ((s,x),a) \<in> construction_origins W"
proof -
  have k: "K2 (construction_assembly xs B W)"
    and result: "R = assembly_output (construction_assembly xs B W)"
    using built by (auto simp: source_constructs_iff_K2)
  have out: "a \<in> rra_carrier (object_structure (assembly_output (construction_assembly xs B W)))"
    using atom result by simp
  obtain c where cp: "c \<in> copied_carrier (assembly_pieces (construction_assembly xs B W))"
    "(c,a) \<in> assembly_origin (construction_assembly xs B W)"
    using K2_no_unexplained_output_atom[OF k out] by blast
  obtain s x where shape: "c = (s,x)" by (cases c) auto
  have copied: "(s,x) \<in> copied_carrier (construction_pieces xs B W)"
    and origin: "((s,x),a) \<in> construction_origins W"
    using cp shape by (simp_all add: construction_assembly_def)
  have slot: "s \<in> piece_slots (construction_pieces xs B W)"
    and inside: "x \<in> rra_carrier (object_structure (piece_at (construction_pieces xs B W) s))"
    using copied by (auto simp: copied_carrier_def)
  obtain T where piece: "(s,T) \<in> piece_graph (construction_pieces xs B W)"
    using slot by (auto simp: piece_slots_def rel_dom_def)
  have sv: "single_valued (piece_graph (construction_pieces xs B W))"
    using built by (simp add: source_constructs_def assembly_relation_def piece_family_formed_def)
  have at: "piece_at (construction_pieces xs B W) s = T"
    unfolding piece_at_def by (rule rel_value_eq[OF sv piece])
  obtain j A S where src: "(s,j,A) \<in> construction_selections W"
    "construction_source_at xs B j S" "T = restrict_object S A"
    using construction_has_no_unexplained_piece[OF built piece] by blast
  show ?thesis
    by (rule exI[of _ s], rule exI[of _ j], rule exI[of _ A],
        rule exI[of _ S], rule exI[of _ x])
       (use src inside at origin in \<open>auto simp: restrict_object_def restrict_structure_def\<close>)
qed

section \<open>Adequacy for every assembly at the supplied source boundary\<close>

definition assembly_has_source_origins ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    's assembly_witness \<Rightarrow> bool" where
  "assembly_has_source_origins xs B A \<longleftrightarrow>
    construction_sources_formed xs B \<and>
    (\<forall>s R. (s,R) \<in> piece_graph (assembly_pieces A) \<longrightarrow>
      (\<exists>j X. source_selection_valid xs B j X \<and>
        R = fragment_material (construction_fragment xs B j X)))"

lemma construction_assembly_has_origins:
  assumes "construction_selection_formed xs B W"
  shows "assembly_has_source_origins xs B (construction_assembly xs B W)"
  using assms
  by (auto simp: assembly_has_source_origins_def construction_assembly_def
    construction_selection_formed_def construction_piece_member; blast)

lemma piece_at_member:
  assumes pf: "piece_family_formed P" and key: "s \<in> piece_slots P"
  shows "(s,piece_at P s) \<in> piece_graph P"
proof -
  obtain R where member: "(s,R) \<in> piece_graph P"
    using key by (auto simp: piece_slots_def rel_dom_def)
  have sv: "single_valued (piece_graph P)" using pf by (simp add: piece_family_formed_def)
  have "piece_at P s = R" unfolding piece_at_def by (rule rel_value_eq[OF sv member])
  then show ?thesis using member by simp
qed

theorem assembly_source_account_complete:
  fixes A :: "'s assembly_witness" and B :: "('b \<times> exact_artifact) set"
  assumes k: "K2 A" and origins: "assembly_has_source_origins xs B A"
  shows "\<exists>W. construction_selection_formed xs B W \<and>
    construction_assembly xs B W = A"
proof -
  let ?P = "assembly_pieces A"
  let ?D = "piece_slots ?P"
  have pf: "piece_family_formed ?P" using k by (simp add: K2_def)
  have sf: "construction_sources_formed xs B"
    using origins by (simp add: assembly_has_source_origins_def)
  have each: "\<forall>s\<in>?D. \<exists>z.
    source_selection_valid xs B (fst z) (snd z) \<and>
    piece_at ?P s = fragment_material (construction_fragment xs B (fst z) (snd z))"
  proof (intro ballI)
    fix s assume key: "s \<in> ?D"
    have member: "(s,piece_at ?P s) \<in> piece_graph ?P"
      by (rule piece_at_member[OF pf key])
    obtain j X where choice: "source_selection_valid xs B j X"
      "piece_at ?P s = fragment_material (construction_fragment xs B j X)"
      using origins member unfolding assembly_has_source_origins_def by blast
    show "\<exists>z. source_selection_valid xs B (fst z) (snd z) \<and>
      piece_at ?P s = fragment_material (construction_fragment xs B (fst z) (snd z))"
      by (rule exI[of _ "(j,X)"]) (use choice in simp)
  qed
  obtain f where f: "\<forall>s\<in>?D.
    source_selection_valid xs B (fst (f s)) (snd (f s)) \<and>
    piece_at ?P s = fragment_material (construction_fragment xs B (fst (f s)) (snd (f s)))"
    using bchoice[OF each] by blast
  let ?W = "\<lparr>construction_selections = graph_map ?D f,
    construction_origins = assembly_origin A\<rparr>"
  have finite: "finite (graph_map ?D f)"
    using piece_slots_finite[OF pf] by (simp add: graph_map_def)
  have valid: "\<forall>s j X. (s,j,X) \<in> graph_map ?D f \<longrightarrow>
    source_selection_valid xs B j X"
  proof (intro allI impI)
    fix s j X assume member: "(s,j,X) \<in> graph_map ?D f"
    have key: "s \<in> ?D" and pair: "f s = (j,X)"
      using member by (auto simp: graph_map_def)
    have chosen: "source_selection_valid xs B (fst (f s)) (snd (f s))"
      using f key by blast
    show "source_selection_valid xs B j X"
      using chosen by (simp only: pair fst_conv snd_conv)
  qed
  have wf: "construction_selection_formed xs B ?W"
    using sf valid finite graph_map_single_valued[of ?D f]
    by (simp add: construction_selection_formed_def)
  have point: "\<And>s R. (s,R) \<in> piece_graph ?P \<Longrightarrow> piece_at ?P s = R"
    unfolding piece_at_def
    by (rule rel_value_eq) (use pf in \<open>auto simp: piece_family_formed_def\<close>)
  have graphs: "piece_graph (construction_pieces xs B ?W) = piece_graph ?P"
  proof (rule set_eqI)
    fix z :: "'s \<times> exact_artifact"
    obtain s R where shape: "z = (s,R)" by (cases z) auto
    show "z \<in> piece_graph (construction_pieces xs B ?W) \<longleftrightarrow> z \<in> piece_graph ?P"
    proof
      assume "z \<in> piece_graph (construction_pieces xs B ?W)"
      then have member: "(s,R) \<in> piece_graph (construction_pieces xs B ?W)"
        using shape by simp
      obtain j X where choice: "(s,j,X) \<in> construction_selections ?W"
        "R = fragment_material (construction_fragment xs B j X)"
        using construction_piece_member[THEN iffD1, OF member] by blast
      have key: "s \<in> ?D" and pair: "f s = (j,X)"
        using choice(1) by (auto simp: graph_map_def)
      have material: "piece_at ?P s =
        fragment_material (construction_fragment xs B (fst (f s)) (snd (f s)))"
        using f key by blast
      have same: "R = piece_at ?P s" using choice(2) material pair by simp
      show "z \<in> piece_graph ?P"
        using piece_at_member[OF pf key] same shape by simp
    next
      assume "z \<in> piece_graph ?P"
      then have member: "(s,R) \<in> piece_graph ?P" using shape by simp
      have key: "s \<in> ?D" using member by (auto simp: piece_slots_def rel_dom_def)
      have selected: "(s,fst (f s),snd (f s)) \<in> construction_selections ?W"
        using key by (simp add: graph_map_def)
      have material: "piece_at ?P s =
        fragment_material (construction_fragment xs B (fst (f s)) (snd (f s)))"
        using f key by blast
      have decoded: "(s,R) \<in> piece_graph (construction_pieces xs B ?W)"
        unfolding construction_piece_member
        by (rule exI[of _ "fst (f s)"], rule exI[of _ "snd (f s)"])
           (use selected material point[OF member] in simp)
      show "z \<in> piece_graph (construction_pieces xs B ?W)" using decoded shape by simp
    qed
  qed
  have same: "construction_pieces xs B ?W = ?P"
    using graphs by (cases "construction_pieces xs B ?W"; cases ?P) simp
  have account: "construction_assembly xs B ?W = A"
    using same by (cases A) (simp add: construction_assembly_def)
  show ?thesis by (rule exI[of _ ?W]) (use wf account in simp)
qed

theorem source_construction_adequate:
  "(\<exists>W :: ('b,'s) source_construction. source_constructs xs B W R) \<longleftrightarrow>
    (\<exists>A :: 's assembly_witness. K2 A \<and> assembly_has_source_origins xs B A \<and>
      R = assembly_output A)"
proof
  assume "\<exists>W :: ('b,'s) source_construction. source_constructs xs B W R"
  then obtain W :: "('b,'s) source_construction" where w: "source_constructs xs B W R" by blast
  show "\<exists>A :: 's assembly_witness. K2 A \<and> assembly_has_source_origins xs B A \<and>
    R = assembly_output A"
    by (rule exI[of _ "construction_assembly xs B W"])
       (use w construction_assembly_has_origins[of xs B W] in
         \<open>auto simp: source_constructs_iff_K2\<close>)
next
  assume "\<exists>A :: 's assembly_witness. K2 A \<and> assembly_has_source_origins xs B A \<and>
    R = assembly_output A"
  then obtain A :: "'s assembly_witness" where a: "K2 A"
    "assembly_has_source_origins xs B A" "R = assembly_output A" by blast
  obtain W where w: "construction_selection_formed xs B W" "construction_assembly xs B W = A"
    using assembly_source_account_complete[OF a(1,2)] by blast
  show "\<exists>W :: ('b,'s) source_construction. source_constructs xs B W R"
    by (rule exI[of _ W]) (use a w in \<open>simp add: source_constructs_iff_K2\<close>)
qed

section \<open>Complete residuals of every declared source\<close>

definition construction_selected_atoms ::
  "('b,'s) source_construction \<Rightarrow> nat + 'b \<Rightarrow> local_address set" where
  "construction_selected_atoms W j = {a. \<exists>s A. (s,j,A) \<in> construction_selections W \<and> a \<in> A}"

definition construction_source_fragment ::
  "exact_artifact list \<Rightarrow> ('b \<times> exact_artifact) set \<Rightarrow>
    ('b,'s) source_construction \<Rightarrow> nat + 'b \<Rightarrow> exact_fragment" where
  "construction_source_fragment xs B W j =
    construction_fragment xs B j (construction_selected_atoms W j)"

lemma construction_complete_source_fragment:
  assumes wf: "construction_selection_formed xs B W"
    and source: "construction_source_at xs B j R"
  shows "fragment_formed (construction_source_fragment xs B W j)"
    and "fragment_source (construction_source_fragment xs B W j) = R"
proof -
  have sf: "construction_sources_formed xs B"
    using wf by (simp add: construction_selection_formed_def)
  have resolved: "construction_source_value xs B j = R" and rf: "exact_formed R"
    using construction_source_value_at[OF sf source] by auto
  have subset: "construction_selected_atoms W j \<subseteq> rra_carrier (object_structure R)"
    using wf resolved
    by (auto simp: construction_selected_atoms_def construction_selection_formed_def source_selection_valid_def)
  have finite: "finite (construction_selected_atoms W j)"
    by (rule finite_subset[OF subset])
       (use rf in \<open>simp add: exact_formed_def object_formed_def rra_formed_def\<close>)
  show "fragment_formed (construction_source_fragment xs B W j)"
    using rf subset finite resolved
    by (simp add: construction_source_fragment_def construction_fragment_def fragment_formed_def)
  show "fragment_source (construction_source_fragment xs B W j) = R"
    using resolved by (simp add: construction_source_fragment_def construction_fragment_def)
qed

lemma construction_source_omission:
  "fragment_omission (construction_source_fragment xs B W j) =
    rra_carrier (object_structure (construction_source_value xs B j)) -
      construction_selected_atoms W j"
  by (simp add: fragment_omission_def construction_source_fragment_def construction_fragment_def)

lemma unselected_source_retained:
  assumes wf: "construction_selection_formed xs B W"
    and source: "construction_source_at xs B j R"
    and unused: "\<And>s A. (s,j,A) \<notin> construction_selections W"
  shows "fragment_material (construction_source_fragment xs B W j) = empty_artifact"
    and "fragment_remainder (construction_source_fragment xs B W j) = R"
proof -
  have selected: "construction_selected_atoms W j = {}"
    using unused by (auto simp: construction_selected_atoms_def)
  have sf: "fragment_formed (construction_source_fragment xs B W j)"
    and resolved: "fragment_source (construction_source_fragment xs B W j) = R"
    using construction_complete_source_fragment[OF wf source] by auto
  show mat: "fragment_material (construction_source_fragment xs B W j) = empty_artifact"
    using selected
    by (simp add: fragment_material_def construction_source_fragment_def
      construction_fragment_def restrict_object_def restrict_structure_def
      internal_incidence_def restrict_basis_def empty_artifact_def empty_basis_def)
  have boundary: "fragment_boundary (construction_source_fragment xs B W j) = {}"
    using selected
    by (simp add: fragment_boundary_def construction_source_fragment_def
      construction_fragment_def crossing_incidence_def touching_incidence_def internal_incidence_def)
  show "fragment_remainder (construction_source_fragment xs B W j) = R"
    using fragment_source_reconstructed[OF sf] resolved mat boundary
    by (simp add: empty_artifact_def empty_basis_def)
qed

text \<open>
  Selection does not erase the source. For each used piece, its source and
  selected carrier recover the exact fragment, including crossing incidence
  and omitted material. The complete source fragment also accounts for atoms
  omitted by every piece, including a declared input from which no piece is
  selected. The fragment reconstruction theorem applies to both projections.

  No output value is accepted as its own origin unless it actually occurs at
  the supplied input or base boundary. Every output atom follows an explicit
  path through a source occurrence, a selected atom, a piece occurrence, and the
  complete assembly origin map.
\<close>

section \<open>Admissible empty output with an explicit unused source boundary\<close>

definition empty_source_construction :: "('b,'s) source_construction" where
  "empty_source_construction = \<lparr>construction_selections={}, construction_origins={}\<rparr>"

lemma source_constructs_empty:
  fixes B :: "('b \<times> exact_artifact) set"
  assumes sources: "construction_sources_formed xs B"
  shows "source_constructs xs B (empty_source_construction :: ('b,'s) source_construction) empty_artifact"
proof -
  let ?W = "empty_source_construction :: ('b,'s) source_construction"
  let ?P = "construction_pieces xs B ?W"
  let ?A = "construction_assembly xs B ?W"
  have pieces: "piece_graph ?P={}" by (simp add: construction_pieces_def empty_source_construction_def)
  have assembly: "K2 ?A"
    using empty_family_assembly[OF pieces]
    by (simp add: construction_assembly_def empty_source_construction_def)
  have selected: "assembly_pieces ?A=?P" by (simp add: construction_assembly_def)
  have result_eq: "assembly_output ?A=empty_artifact"
    using empty_family_output(2)[OF pieces assembly selected] by (simp add: empty_artifact_def)
  have formed: "construction_selection_formed xs B ?W"
    using sources by (simp add: construction_selection_formed_def empty_source_construction_def single_valued_def)
  show ?thesis using formed assembly result_eq by (simp add: source_constructs_iff_K2)
qed

end
