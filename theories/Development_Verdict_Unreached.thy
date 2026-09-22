theory Development_Verdict_Unreached
imports Development_Verdict_Mentions Isabelle_Native_Reach Development_State_Presenter
begin

section \<open>The field \<open>unreached\<close>: every row of a state is reached from its roots\<close>

text \<open>
  The last field of the verdict's build order, and the only one composing the reach. A state's rows are
  reached from its roots through the mentions of the rows that reach them: a constant is reached when a root
  heads it, or when a row mentioning it is a statement of a reached constant. That closure is the native
  reach of \<open>Native_Table_Reach\<close>, consumed with its contract (\<open>native_reached_exact\<close>) and not rebuilt; what
  this theory adds is the reach table read from the presented rows, keyed by the state's own constant keys,
  its fidelity to the reach of the state (\<open>isabelle_reached_constants\<close>, through \<open>isabelle_reach_table_exact\<close>),
  and the row reading of the field: a row is reached when a constant it declares or a constant it is a
  statement of is reached. Acceptance reads that every row is reached; the unreached rows, the witness,
  need store absence and are built later, and neither is defined as the other's negation.
\<close>

section \<open>The reach table over the state's constant keys\<close>

text \<open>
  The table holds a row at every atom key of the state: it is a root when a root row mentions it, and its
  predecessors are the keys of the subjects of the rows mentioning it. The predecessors of a key are the
  index of mentions by constant: request construction reads the same table when it checks that every
  support key is mentioned by a row about the subject. The row values are functions of the key, so the
  table is single-valued whatever the atoms.
\<close>

definition state_root_keys :: "'j state_family \<Rightarrow> state_key list" where
  "state_root_keys Rs=concat (map (\<lambda>z. row_mentions (snd z)) Rs)"

definition state_reach_predecessors :: "'i state_family list \<Rightarrow> state_key \<Rightarrow> state_key list" where
  "state_reach_predecessors Fs a=concat (map (\<lambda>F. concat (map (\<lambda>z. row_subjects (snd z)) (mention_fibre a F))) Fs)"

definition state_reach_table ::
    "(state_key\<times>'n) list \<Rightarrow> 'j state_family \<Rightarrow> 'i state_family list \<Rightarrow> reach_table" where
  "state_reach_table A Rs Fs=map (\<lambda>a. (fst a,fst a\<in>set (state_root_keys Rs),state_reach_predecessors Fs (fst a))) A"

lemma state_root_keys_member:
  "k\<in>set (state_root_keys Rs) \<longleftrightarrow> (\<exists>q\<in>set (map snd Rs). k\<in>set (row_mentions q))"
  by (auto simp: state_root_keys_def)

lemma state_reach_predecessors_member:
  "p\<in>set (state_reach_predecessors Fs a) \<longleftrightarrow>
    (\<exists>F\<in>set Fs. \<exists>z\<in>set F. a\<in>set (row_mentions (snd z)) \<and> p\<in>set (row_subjects (snd z)))"
  by (auto simp: state_reach_predecessors_def key_fibre_def) (metis snd_conv)+

text \<open>The row lemma: the predecessors of a key are the keys of the subjects of the rows mentioning it.\<close>

theorem state_reach_table_row:
  "(k,r,ps)\<in>set (state_reach_table A Rs Fs) \<longleftrightarrow>
    k\<in>fst ` set A \<and> r=(k\<in>set (state_root_keys Rs)) \<and> ps=state_reach_predecessors Fs k"
  by (auto simp: state_reach_table_def)

lemma state_reach_table_formed: "reach_table_formed (state_reach_table A Rs Fs)"
  unfolding reach_table_formed_def single_valued_def by (auto simp: state_reach_table_row)

section \<open>The families of a state, every kind once\<close>

definition state_families :: "state_rows \<Rightarrow> isabelle_context state_family list" where
  "state_families R=map (state_entities R) entity_kinds"

lemma state_families_range: "set (state_families R)=range (state_entities R)"
  by (simp add: state_families_def entity_kinds_all)

section \<open>The state's reach, read from its pairs\<close>

lemma isabelle_entity_reach_pairs_member:
  "(c,s)\<in>set (isabelle_entity_reach_pairs C e) \<longleftrightarrow> c\<in>set (entity_mentions e) \<and>
    s\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)"
  by (cases "isabelle_specified_proposition e") (auto simp: isabelle_entity_reach_pairs_def entity_mentions_def)

lemma isabelle_reach_pairs_member:
  "(c,s)\<in>set (isabelle_reach_pairs C) \<longleftrightarrow> (\<exists>e\<in>set (snd C). c\<in>set (entity_mentions e) \<and>
    s\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))"
  by (auto simp: isabelle_reach_pairs_def isabelle_entity_reach_pairs_member)

lemma isabelle_reach_predecessors_member:
  "s\<in>set (isabelle_reach_predecessors C c) \<longleftrightarrow> (c,s)\<in>set (isabelle_reach_pairs C)"
  by (force simp: isabelle_reach_predecessors_def)

lemma isabelle_reach_heads_member:
  "c\<in>set (isabelle_reach_heads roots) \<longleftrightarrow> (\<exists>t\<in>set roots. c\<in>set (root_mentions t))"
  by (auto simp: isabelle_reach_heads_def map_filter_member root_mentions_def split: option.splits; metis)

lemma isabelle_reach_constants_member:
  "c\<in>set (isabelle_reach_constants roots C) \<longleftrightarrow>
    c\<in>set (isabelle_reach_heads roots) \<or> (\<exists>s. (c,s)\<in>set (isabelle_reach_pairs C))"
  by (force simp: isabelle_reach_constants_def)

section \<open>The reach table of the rows is the reach of the state\<close>

context
  fixes key :: "nat \<Rightarrow> state_key" and S :: isabelle_rooted_context and R :: state_rows
    and Fs :: "isabelle_context state_family list"
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
begin

private lemma inj: "inj_on key {..<length (fst (snd S))}"
  by (rule atoms_present_key_injective[OF state_presents_atoms[OF present]])

private lemma inside:
  "e\<in>set (snd (snd S)) \<Longrightarrow> d\<in>set (entity_mentions e) \<Longrightarrow> d<length (fst (snd S))"
  "e\<in>set (snd (snd S)) \<Longrightarrow>
    d\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e) \<Longrightarrow>
    d<length (fst (snd S))"
  "t\<in>set (fst S) \<Longrightarrow> d\<in>set (root_mentions t) \<Longrightarrow> d<length (fst (snd S))"
  using entity_mentions_positions isabelle_entity_subjects_positions root_mentions_positions
    state_presents_inside[OF present] by (force simp: state_positions_def)+

private lemma key_member:
  assumes "c<length (fst (snd S))" "set ds\<subseteq>{..<length (fst (snd S))}"
  shows "key c\<in>key ` set ds \<longleftrightarrow> c\<in>set ds"
  using inj_on_image_mem_iff[OF inj, of c "set ds"] assms by simp

private lemma atom:
  "k\<in>fst ` set (state_atoms R) \<longleftrightarrow> (\<exists>d<length (fst (snd S)). k=key d)"
  using state_presents_atoms[OF present] unfolding atoms_present_def by (force simp: image_image)

private lemma root_at:
  assumes bound: "c<length (fst (snd S))"
  shows "key c\<in>set (state_root_keys (state_roots R)) \<longleftrightarrow> c\<in>set (isabelle_reach_heads (fst S))"
proof -
  have "key c\<in>set (state_root_keys (state_roots R)) \<longleftrightarrow>
      (\<exists>t\<in>set (fst S). key c\<in>key ` set (root_mentions t))"
    by (simp add: state_root_keys_member state_presents_root_family[OF present])
  also have "\<dots> \<longleftrightarrow> (\<exists>t\<in>set (fst S). c\<in>set (root_mentions t))"
    using key_member[OF bound] inside(3) by blast
  finally show ?thesis by (simp add: isabelle_reach_heads_member)
qed

private lemma predecessor_at:
  assumes bound: "c<length (fst (snd S))"
  shows "p\<in>set (state_reach_predecessors Fs (key c)) \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). \<exists>s. p=key s \<and>
    c\<in>set (entity_mentions e) \<and>
    s\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e))"
proof -
  have "p\<in>set (state_reach_predecessors Fs (key c)) \<longleftrightarrow>
      (\<exists>q\<in>(\<Union>F\<in>set Fs. set (map snd F)). key c\<in>set (row_mentions q) \<and> p\<in>set (row_subjects q))"
    by (force simp: state_reach_predecessors_member)
  also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). key c\<in>key ` set (entity_mentions e) \<and>
      p\<in>key ` set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e))"
    by (simp only: state_families_rows[OF present families]) auto
  also have "\<dots> \<longleftrightarrow> (\<exists>e\<in>set (snd (snd S)). c\<in>set (entity_mentions e) \<and>
      p\<in>key ` set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e))"
    using key_member[OF bound] inside(1) by blast
  finally show ?thesis by blast
qed

private lemma complete:
  assumes reached: "c\<in>isabelle_reached_constants (fst S) (snd S)"
  shows "key c\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) Fs)"
proof -
  let ?g="key \<circ> inv natural_binary_digits"
  have inv: "inv natural_binary_digits (natural_binary_digits d)=d" for d
    using state_constant_key_injective by (simp add: state_constant_key_def inv_f_f)
  have g: "?g (natural_binary_digits d)=key d" for d by (simp add: inv)
  have "?g (natural_binary_digits c)\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) Fs)"
  proof (rule table_reached_simulation[where T="isabelle_reach_table (fst S) (snd S)" and g="?g"
      and k="natural_binary_digits c"])
    show "natural_binary_digits c\<in>table_reached (isabelle_reach_table (fst S) (snd S))"
      using reached isabelle_reach_table_exact by blast
    fix k r ps assume row: "(k,r,ps)\<in>set (isabelle_reach_table (fst S) (snd S))"
    obtain d where k: "k=natural_binary_digits d" and listed: "d\<in>set (isabelle_reach_constants (fst S) (snd S))"
      and r: "r=(d\<in>set (isabelle_reach_heads (fst S)))"
      and ps: "ps=map natural_binary_digits (isabelle_reach_predecessors (snd S) d)"
      using row by (auto simp: isabelle_reach_table_row)
    have bound: "d<length (fst (snd S))"
      using listed inside(1,3)
      by (auto simp: isabelle_reach_constants_member isabelle_reach_heads_member isabelle_reach_pairs_member)
    show "\<exists>r' ps'. (?g k,r',ps')\<in>set (state_reach_table (state_atoms R) (state_roots R) Fs) \<and> (r\<longrightarrow>r') \<and>
        ?g ` set ps\<subseteq>set ps'"
    proof (intro exI conjI)
      show "(?g k,key d\<in>set (state_root_keys (state_roots R)),state_reach_predecessors Fs (key d))
          \<in>set (state_reach_table (state_atoms R) (state_roots R) Fs)"
        using bound by (auto simp: k inv state_reach_table_row atom)
      show "r\<longrightarrow>key d\<in>set (state_root_keys (state_roots R))" using root_at[OF bound] r by simp
      show "?g ` set ps\<subseteq>set (state_reach_predecessors Fs (key d))"
      proof
        fix p assume "p\<in>?g ` set ps"
        then obtain s where p: "p=key s" and pred: "s\<in>set (isabelle_reach_predecessors (snd S) d)"
          by (auto simp: ps inv)
        then show "p\<in>set (state_reach_predecessors Fs (key d))"
          by (auto simp: predecessor_at[OF bound] isabelle_reach_predecessors_member isabelle_reach_pairs_member)
      qed
    qed
  qed
  then show ?thesis by (simp add: inv)
qed

private lemma sound:
  assumes bound: "c<length (fst (snd S))"
    and reached: "key c\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) Fs)"
  shows "c\<in>isabelle_reached_constants (fst S) (snd S)"
proof -
  let ?n="length (fst (snd S))"
  let ?g="natural_binary_digits \<circ> inv_into {..<?n} key"
  have ginv: "inv_into {..<?n} key (key d)=d" if "d<?n" for d
    using inv_into_f_f[OF inj] that by simp
  have g: "?g (key d)=natural_binary_digits d" if "d<?n" for d using ginv[OF that] by simp
  have "?g (key c)\<in>table_reached (isabelle_reach_table (fst S) (snd S))"
  proof (rule table_reached_simulation[where g="?g", OF _ reached])
    fix k r ps assume row: "(k,r,ps)\<in>set (state_reach_table (state_atoms R) (state_roots R) Fs)"
      and live: "r \<or> ps\<noteq>[]"
    obtain d where bd: "d<?n" and k: "k=key d" and r: "r=(key d\<in>set (state_root_keys (state_roots R)))"
      and ps: "ps=state_reach_predecessors Fs (key d)"
      using row by (auto simp: state_reach_table_row atom)
    have listed: "d\<in>set (isabelle_reach_constants (fst S) (snd S))"
    proof (cases r)
      case True then show ?thesis using root_at[OF bd] r by (simp add: isabelle_reach_constants_member)
    next
      case False
      then obtain p where "p\<in>set ps" using live by (cases ps) auto
      then show ?thesis
        by (auto simp: ps predecessor_at[OF bd] isabelle_reach_constants_member isabelle_reach_pairs_member)
    qed
    show "\<exists>r' ps'. (?g k,r',ps')\<in>set (isabelle_reach_table (fst S) (snd S)) \<and> (r\<longrightarrow>r') \<and> ?g ` set ps\<subseteq>set ps'"
    proof (intro exI conjI)
      show "(?g k,d\<in>set (isabelle_reach_heads (fst S)),map natural_binary_digits (isabelle_reach_predecessors (snd S) d))
          \<in>set (isabelle_reach_table (fst S) (snd S))"
        using listed by (auto simp: k ginv[OF bd] isabelle_reach_table_row)
      show "r\<longrightarrow>d\<in>set (isabelle_reach_heads (fst S))" using root_at[OF bd] r by simp
      show "?g ` set ps\<subseteq>set (map natural_binary_digits (isabelle_reach_predecessors (snd S) d))"
      proof
        fix q assume "q\<in>?g ` set ps"
        then obtain p where q: "q=?g p" and p: "p\<in>set ps" by blast
        obtain e s where e: "e\<in>set (snd (snd S))" and ps': "p=key s" and m: "d\<in>set (entity_mentions e)"
          and sj: "s\<in>set (isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e)"
          using p by (auto simp: ps predecessor_at[OF bd])
        have "?g p=natural_binary_digits s" using ginv[OF inside(2)[OF e sj]] ps' by simp
        moreover have "s\<in>set (isabelle_reach_predecessors (snd S) d)"
          using e m sj by (auto simp: isabelle_reach_predecessors_member isabelle_reach_pairs_member)
        ultimately show "q\<in>set (map natural_binary_digits (isabelle_reach_predecessors (snd S) d))"
          using q by simp
      qed
    qed
  qed
  then show ?thesis using isabelle_reach_table_exact ginv[OF bound] by simp
qed

theorem state_reach_table_exact:
  assumes bound: "c<length (fst (snd S))"
  shows "key c\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) Fs) \<longleftrightarrow>
    c\<in>isabelle_reached_constants (fst S) (snd S)"
  using sound[OF bound] complete by blast

end

section \<open>A row is reached\<close>

text \<open>
  A row is reached when some key it declares, or some key it is a statement of, is reached in the table
  the call carries: two rules at one site, each reading one citation list through \<open>some\<close> over the reach.
\<close>

definition row_declared_reached_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_declared_reached_rule s=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition row_subject_reached_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "row_subject_reached_rule s=finite_native_rule
    (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5))
    [([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))]"

definition row_reached_rules :: "'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "row_reached_rules s=[([0],row_declared_reached_rule s),([1],row_subject_reached_rule s)]"

locale row_reached_program = native_rule_family P r "row_reached_rules s" + somes: native_some_program P s el
  for P :: "'u native_system" and r s el :: "'u definition_site"
begin

sublocale law: native_rule_law P r "row_reached_rules s"
  by (rule native_rule_lawI[OF native_rule_family_axioms])
    (auto simp: row_reached_rules_def row_declared_reached_rule_def row_subject_reached_rule_def)

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term x (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> term_formed x \<and>
    ((\<exists>h\<in>set (row_declared (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P) \<or>
     (\<exists>h\<in>set (row_subjects (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P))"
proof
  assume "(r,Pair_Term x (state_row_term ident z))\<in>positive_meaning P"
  then obtain c p ps f where rule: "(c,finite_native_rule p ps)\<in>set (row_reached_rules s)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term x (state_row_term ident z)"
    and support: "\<forall>(k,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    unfolding law.exact by (elim exE conjE) (rule that; assumption)
  have p: "p=row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3) (native_var 4) (native_var 5)"
    using rule by (auto simp: row_reached_rules_def row_declared_reached_rule_def row_subject_reached_rule_def
      finite_native_rule_eq_iff)
  have fields: "f [0]=x" "f [2]=keys_term (row_declared (snd z))" "f [3]=keys_term (row_subjects (snd z))"
    using shape by (simp_all add: p row_pattern_def state_row_term_def)
  from rule consider "set ps={([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 2)))}"
      | "set ps={([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))}"
    by (auto simp: row_reached_rules_def row_declared_reached_rule_def row_subject_reached_rule_def
      finite_native_rule_eq_iff)
  then show "term_formed x \<and>
    ((\<exists>h\<in>set (row_declared (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P) \<or>
     (\<exists>h\<in>set (row_subjects (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P))"
  proof cases
    case 1
    have "(s,Pair_Term (f [0]) (f [2]))\<in>positive_meaning P" using support 1 by auto
    then show ?thesis by (auto simp: fields keys_term_def somes.exact)
  next
    case 2
    have "(s,Pair_Term (f [0]) (f [3]))\<in>positive_meaning P" using support 2 by auto
    then show ?thesis by (auto simp: fields keys_term_def somes.exact)
  qed
next
  assume both: "term_formed x \<and>
    ((\<exists>h\<in>set (row_declared (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P) \<or>
     (\<exists>h\<in>set (row_subjects (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P))"
  have formed: "term_formed x" using both by blast
  from both consider (declared) "\<exists>h\<in>set (row_declared (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P"
    | (subject) "\<exists>h\<in>set (row_subjects (snd z)). (el,Pair_Term x (path_term h))\<in>positive_meaning P" by blast
  then show "(r,Pair_Term x (state_row_term ident z))\<in>positive_meaning P"
  proof cases
    case declared
    have "(r,evaluate_pattern (native_values [x,path_term (fst z),keys_term (row_declared (snd z)),
        keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))])
        (decode_finite_pattern (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3)
          (native_var 4) (native_var 5))))\<in>positive_meaning P"
      by (rule law.step_at[where c="[0]" and ps="[([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
        (use declared formed identity in \<open>simp_all add: row_reached_rules_def row_declared_reached_rule_def
          row_pattern_def keys_term_def somes.exact data_list_term_formed insert_Diff_if\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def)
  next
    case subject
    have "(r,evaluate_pattern (native_values [x,path_term (fst z),keys_term (row_declared (snd z)),
        keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))])
        (decode_finite_pattern (row_pattern (native_var 0) (native_var 1) (native_var 2) (native_var 3)
          (native_var 4) (native_var 5))))\<in>positive_meaning P"
      by (rule law.step_at[where c="[1]" and ps="[([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 3)))]"])
        (use subject formed identity in \<open>simp_all add: row_reached_rules_def row_subject_reached_rule_def
          row_pattern_def keys_term_def somes.exact data_list_term_formed insert_Diff_if\<close>)
    then show ?thesis by (simp add: row_pattern_def state_row_term_def)
  qed
qed

end

section \<open>The program of the field\<close>

text \<open>
  The program holds the reach's own definitions at their own sites, unchanged, and the field's four
  definitions at sites of their own; the two programs agree on the reach's sites, so the reach keeps its
  meaning here (@{thm positive_meaning_shared_definitions}) and no argument about it is made again.
\<close>

abbreviation verdict_reached_some :: "local_address option definition_site" where
  "verdict_reached_some \<equiv> (Some [],[34])"
abbreviation verdict_row_reached :: "local_address option definition_site" where
  "verdict_row_reached \<equiv> (Some [],[35])"
abbreviation verdict_reached_family :: "local_address option definition_site" where
  "verdict_reached_family \<equiv> (Some [],[36])"
abbreviation verdict_unreached :: "local_address option definition_site" where
  "verdict_unreached \<equiv> (Some [],[37])"

definition verdict_unreached_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "verdict_unreached_definitions=reach_definitions@[
    (verdict_reached_some,native_some_rules verdict_reached_some reach_reached),
    (verdict_row_reached,row_reached_rules verdict_reached_some),
    (verdict_reached_family,native_every_rules verdict_reached_family verdict_row_reached),
    (verdict_unreached,native_every_rules verdict_unreached verdict_reached_family)]"

definition finite_verdict_unreached :: "local_address option finite_native_system" where
  "finite_verdict_unreached=finite_rule_program verdict_unreached_definitions"

definition verdict_unreached_system :: "local_address option native_system" where
  "verdict_unreached_system=decode_finite_system finite_verdict_unreached"

lemma finite_verdict_unreached_formed: "finite_system_formed finite_verdict_unreached"
  by code_simp

lemma verdict_unreached_formed: "schema_system_formed verdict_unreached_system"
  using finite_verdict_unreached_formed
  by (simp only: verdict_unreached_system_def finite_system_formed_correct)

lemma verdict_unreached_family:
  assumes member: "(d,rs)\<in>set verdict_unreached_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family verdict_unreached_system d rs"
  unfolding verdict_unreached_system_def finite_verdict_unreached_def
  by (rule finite_rule_program_family[OF verdict_unreached_formed[unfolded verdict_unreached_system_def
    finite_verdict_unreached_def] _ member plain])
    (simp add: verdict_unreached_definitions_def reach_definitions_def)

lemmas verdict_unreached_rule_defs = verdict_unreached_definitions_def reach_definitions_def
  native_some_rules_def native_some_first_def native_some_rest_def native_every_rules_def
  native_every_nil_def native_every_step_def row_reached_rules_def row_declared_reached_rule_def
  row_subject_reached_rule_def

lemma verdict_unreached_reach:
  assumes site: "d\<in>{reach_reached,reach_search,reach_holds,reach_some}"
  shows "(d,t)\<in>positive_meaning verdict_unreached_system \<longleftrightarrow> (d,t)\<in>positive_meaning native_reach_system"
  unfolding verdict_unreached_system_def finite_verdict_unreached_def native_reach_system_def finite_native_reach_def
  by (rule finite_rule_program_join[OF verdict_unreached_formed[unfolded verdict_unreached_system_def
    finite_verdict_unreached_def] _ native_reach_formed[unfolded native_reach_system_def finite_native_reach_def]])
    (use site in \<open>simp_all add: verdict_unreached_definitions_def reach_definitions_def\<close>)

lemma verdict_unreached_reached:
  assumes formed: "reach_table_formed T"
  shows "(reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    bs\<in>table_reached T"
proof -
  have "(reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
      (reach_reached,Pair_Term (reach_table_term T) (path_term bs))\<in>positive_meaning native_reach_system"
    by (rule verdict_unreached_reach) simp
  also have "\<dots> \<longleftrightarrow> bs\<in>table_reached T" by (rule native_reached_exact[OF formed])
  finally show ?thesis .
qed

interpretation reached_rows: row_reached_program verdict_unreached_system verdict_row_reached verdict_reached_some
    reach_reached
  unfolding row_reached_program_def native_some_program_def
  by (intro conjI; rule verdict_unreached_family) (simp_all add: verdict_unreached_rule_defs)

interpretation reached_families: native_every_program verdict_unreached_system verdict_reached_family
    verdict_row_reached
  unfolding native_every_program_def
  by (rule verdict_unreached_family) (simp_all add: verdict_unreached_rule_defs)

interpretation reached_selections: native_every_program verdict_unreached_system verdict_unreached
    verdict_reached_family
  unfolding native_every_program_def
  by (rule verdict_unreached_family) (simp_all add: verdict_unreached_rule_defs)

section \<open>The field \<open>unreached\<close>, over any selection and any reach table\<close>

theorem native_unreached_rows:
  assumes formed: "reach_table_formed T" and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_unreached,Pair_Term (reach_table_term T) (state_families_term ident Fs))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (\<forall>F\<in>set Fs. \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)). h\<in>table_reached T)"
proof -
  interpret reading: selection_every_reading verdict_unreached_system verdict_unreached verdict_reached_family
      verdict_row_reached reach_table_term ident "\<lambda>T z. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
        (reach_reached,Pair_Term (reach_table_term T) (path_term h))\<in>positive_meaning verdict_unreached_system"
    by unfold_locales (auto simp: identity reached_rows.exact[OF identity])
  show ?thesis using verdict_unreached_reached[OF formed] by (simp add: reading.exact)
qed

section \<open>The field \<open>unreached\<close> of a presented state\<close>

lemma entity_reached_rows:
  "isabelle_entity_reached Rs C e \<longleftrightarrow>
    (\<exists>d\<in>set (entity_declared e)\<union>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e). d\<in>Rs)"
proof (cases "isabelle_declared_constant e")
  case None
  then show ?thesis by (auto simp: isabelle_entity_reached_def entity_declared_def list_ex_iff)
next
  case (Some c)
  have "isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e=[]"
    using Some by (cases e) simp_all
  then show ?thesis using Some by (simp add: isabelle_entity_reached_def entity_declared_def)
qed

lemma unreached_entities_empty:
  "isabelle_unreached_entities roots C=[] \<longleftrightarrow>
    (\<forall>e\<in>set (snd C). isabelle_entity_reached (isabelle_reached_constants roots C) C e)"
  by (auto simp: isabelle_unreached_entities_def Let_def filter_empty_conv)

theorem native_unreached_exact:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_unreached,Pair_Term (reach_table_term (state_reach_table (state_atoms R) (state_roots R) Fs))
      (state_families_term ident Fs))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    isabelle_unreached_entities (fst S) (snd S)=[]"
proof -
  let ?T="state_reach_table (state_atoms R) (state_roots R) Fs" and ?n="length (fst (snd S))"
    and ?sj="\<lambda>e. isabelle_entity_subjects (fst (snd S)) (isabelle_development_constants (snd (snd S))) e"
  have inside: "\<And>e d. e\<in>set (snd (snd S)) \<Longrightarrow> d\<in>set (entity_declared e)\<union>set (?sj e) \<Longrightarrow> d<?n"
    using entity_declared_positions isabelle_entity_subjects_positions state_presents_inside[OF present]
    by (force simp: state_positions_def)
  have "(verdict_unreached,Pair_Term (reach_table_term ?T) (state_families_term ident Fs))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
      (\<forall>q\<in>(\<Union>F\<in>set Fs. set (map snd F)). \<exists>h\<in>set (row_declared q)\<union>set (row_subjects q). h\<in>table_reached ?T)"
    by (simp add: native_unreached_rows[OF state_reach_table_formed identity])
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). \<exists>d\<in>set (entity_declared e)\<union>set (?sj e). key d\<in>table_reached ?T)"
    by (simp only: state_families_rows[OF present families]) (simp add: bex_Un)
  also have "\<dots> \<longleftrightarrow> (\<forall>e\<in>set (snd (snd S)). \<exists>d\<in>set (entity_declared e)\<union>set (?sj e).
      d\<in>isabelle_reached_constants (fst S) (snd S))"
    using state_reach_table_exact[OF present families] inside by (metis (no_types, lifting))
  also have "\<dots> \<longleftrightarrow> isabelle_unreached_entities (fst S) (snd S)=[]"
    by (simp add: unreached_entities_empty entity_reached_rows)
  finally show ?thesis .
qed

text \<open>
  The contract states exactly the unreached member of the context assessment: its fourth component is empty.
\<close>

corollary native_unreached_assessment:
  assumes present: "state_presents key S R" and families: "set Fs=range (state_entities R)"
    and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_unreached,Pair_Term (reach_table_term (state_reach_table (state_atoms R) (state_roots R) Fs))
      (state_families_term ident Fs))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (case isabelle_context_assessment (fst S) (snd S) of (u,d,m,r,f) \<Rightarrow> r={||})"
proof -
  have empty: "fset_of_list xs={||} \<longleftrightarrow> xs=[]" for xs :: "isabelle_entity list" by (cases xs) simp_all
  show ?thesis
    by (simp add: native_unreached_exact[OF present families identity] isabelle_context_assessment_def empty)
qed

text \<open>The presenter's rows, read with every kind's family once.\<close>

corollary native_unreached_presented:
  assumes presented: "state_presenter S=Some R" and identity: "\<And>y. term_formed (ident y)"
  shows "(verdict_unreached,Pair_Term (reach_table_term (state_reach_table (state_atoms R) (state_roots R)
      (state_families R))) (state_families_term ident (state_families R)))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    isabelle_unreached_entities (fst S) (snd S)=[]"
  by (rule native_unreached_exact[OF state_presenter_presents[OF presented] state_families_range identity])

end
