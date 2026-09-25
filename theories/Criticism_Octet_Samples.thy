theory Criticism_Octet_Samples
  imports Criticism_Samples Factor_Finite_Payload_Literals Factor_System_Restriction
    RRA_Finite_Fresh_Addresses Factor_Finite_Artifact_Enumeration Factor_Executable_Artifact_Values
    Factor_Artifact_Values Bootstrap_Finite_Closure Native_Control_Quotation_Code Tree_Map_Indexes
begin

section \<open>The octets a term carries and the targets a program states\<close>

text \<open>
  An octet occurs in a term as a payload leaf, or inside a target leaf as an address or an attachment
  value of its artifact, or as the address of an occurrence anchor; the artifact's octets are read
  from its canonical rows. The targets a program states are read from its patterns as its payloads are
  (\<open>Factor_Finite_Payload_Literals\<close>), and they are exactly the target leaves of its decoding.
\<close>

definition artifact_rows_octets :: "artifact_value_rows \<Rightarrow> octets list" where
  "artifact_rows_octets q=(case q of (A,E,B,F) \<Rightarrow> A @ concat (map (\<lambda>(r,p,x). [r,p,x]) E) @
    concat (map (\<lambda>(a,v). [a,v]) B) @ concat (map (\<lambda>(a,v). [a,v]) F))"

fun finite_target_octets :: "finite_exact_target \<Rightarrow> octets fset" where
  "finite_target_octets (Finite_Whole C)=fset_of_list (artifact_rows_octets (finite_artifact_rows C))"
| "finite_target_octets (Finite_Anchor C a)=finsert a (fset_of_list (artifact_rows_octets (finite_artifact_rows C)))"

fun finite_term_octets :: "finite_factor_term \<Rightarrow> octets fset" where
  "finite_term_octets (Finite_Target t)=finite_target_octets t"
| "finite_term_octets (Finite_Payload v)={|v|}"
| "finite_term_octets (Finite_Pair x y)=finite_term_octets x |\<union>| finite_term_octets y"

definition criticism_term_octets :: "finite_factor_term list \<Rightarrow> octets fset" where
  "criticism_term_octets ts=ffUnion (fset_of_list (map finite_term_octets ts))"

fun finite_pattern_targets :: "'a finite_term_pattern \<Rightarrow> finite_exact_target fset" where
  "finite_pattern_targets (Finite_Variable a)={||}"
| "finite_pattern_targets (Finite_Pattern_Target t)={|t|}"
| "finite_pattern_targets (Finite_Pattern_Payload v)={||}"
| "finite_pattern_targets (Finite_Pattern_Pair p q)=finite_pattern_targets p |\<union>| finite_pattern_targets q"

lemma finite_pattern_targets_exact:
  "t |\<in>| finite_pattern_targets p \<longleftrightarrow> Target_Term (decode_finite_target t) \<in> pattern_leaves (decode_finite_pattern p)"
  by (induction p) auto

definition finite_material_targets :: "'a finite_material_pattern \<Rightarrow> finite_exact_target fset" where
  "finite_material_targets M=finite_pattern_targets (finite_material_source M) |\<union>|
    finite_pattern_targets (finite_material_atoms M) |\<union>| finite_pattern_targets (finite_material_edges M) |\<union>|
    finite_pattern_targets (finite_material_counts M) |\<union>| finite_pattern_targets (finite_material_functions M)"

lemma finite_material_targets_exact:
  "t |\<in>| finite_material_targets M \<longleftrightarrow> Target_Term (decode_finite_target t) \<in> material_leaves (decode_finite_material M)"
  by (auto simp: finite_material_targets_def material_leaves_def material_fields_def
    decode_finite_material_def finite_pattern_targets_exact)

definition finite_schema_targets :: "('a,'s,'d) finite_factor_schema \<Rightarrow> finite_exact_target fset" where
  "finite_schema_targets S=finite_pattern_targets (finite_schema_conclusion S) |\<union>|
    ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_targets p) (finite_schema_premises S)) |\<union>|
    ffUnion (fimage (\<lambda>(s,M). finite_material_targets M) (finite_schema_materials S))"

lemma finite_schema_targets_exact:
  "t |\<in>| finite_schema_targets S \<longleftrightarrow> Target_Term (decode_finite_target t) \<in> schema_leaves (decode_finite_schema S)"
proof -
  have calls: "t |\<in>| ffUnion (fimage (\<lambda>(s,d,p). finite_pattern_targets p) (finite_schema_premises S)) \<longleftrightarrow>
    Target_Term (decode_finite_target t) \<in> (\<Union>(s,d,p)\<in>schema_premises (decode_finite_schema S). pattern_leaves p)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_pattern_targets_exact decode_finite_call_pattern_def
      map_relation_values_def split: prod.splits; force)
  have materials: "t |\<in>| ffUnion (fimage (\<lambda>(s,M). finite_material_targets M) (finite_schema_materials S)) \<longleftrightarrow>
    Target_Term (decode_finite_target t) \<in> (\<Union>(s,M)\<in>schema_material_premises (decode_finite_schema S). material_leaves M)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_material_targets_exact map_relation_values_def
      split: prod.splits; force)
  show ?thesis using calls materials
    by (simp add: finite_schema_targets_def schema_leaves_def finite_pattern_targets_exact)
qed

definition finite_system_targets :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_exact_target fset" where
  "finite_system_targets P=
    ffUnion (fimage (\<lambda>(d,p). finite_pattern_targets p) (finite_system_interfaces P)) |\<union>|
    ffUnion (fimage (\<lambda>(dc,S). finite_schema_targets S) (finite_system_clauses P))"

theorem finite_system_targets_exact:
  "t |\<in>| finite_system_targets P \<longleftrightarrow> Target_Term (decode_finite_target t) \<in> system_leaves (decode_finite_system P)"
proof -
  have interfaces: "t |\<in>| ffUnion (fimage (\<lambda>(d,p). finite_pattern_targets p) (finite_system_interfaces P)) \<longleftrightarrow>
    Target_Term (decode_finite_target t) \<in> (\<Union>(d,p)\<in>system_interfaces (decode_finite_system P). pattern_leaves p)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_pattern_targets_exact map_relation_values_def
      split: prod.splits; force)
  have clauses: "t |\<in>| ffUnion (fimage (\<lambda>(dc,S). finite_schema_targets S) (finite_system_clauses P)) \<longleftrightarrow>
    Target_Term (decode_finite_target t) \<in> (\<Union>(dc,S)\<in>system_clauses (decode_finite_system P). schema_leaves S)"
    by (auto simp: ffUnion.rep_eq fimage.rep_eq finite_schema_targets_exact map_relation_values_def
      split: prod.splits; force)
  show ?thesis using interfaces clauses by (simp add: finite_system_targets_def system_leaves_def)
qed

lemma pattern_leaves_not_pair: "Pair_Term x y \<notin> pattern_leaves p"
  by (induction p) auto

lemma system_leaves_not_pair: "Pair_Term x y \<notin> system_leaves P"
  by (fastforce simp: system_leaves_def schema_leaves_def material_leaves_def pattern_leaves_not_pair)

lemma system_leaves_restriction: "system_leaves (system_restriction P U) \<subseteq> system_leaves P"
  by (fastforce simp: system_leaves_def system_restriction_def)

text \<open>A leaf of a finite term is stated by a finite program exactly when its decoding is stated by the decoded program.\<close>

fun finite_leaf_stated_in :: "octets fset \<Rightarrow> finite_exact_target fset \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_leaf_stated_in S T (Finite_Target t)=(t |\<in>| T)"
| "finite_leaf_stated_in S T (Finite_Payload v)=(v |\<in>| S)"
| "finite_leaf_stated_in S T (Finite_Pair x y)=False"

definition finite_leaf_stated :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_leaf_stated P=finite_leaf_stated_in (finite_system_payloads P) (finite_system_targets P)"

lemma finite_leaf_stated_exact:
  "finite_leaf_stated P y \<longleftrightarrow> decode_finite_term y \<in> system_leaves (decode_finite_system P)"
proof (cases y)
  case (Finite_Target t)
  then show ?thesis by (simp add: finite_leaf_stated_def finite_system_targets_exact)
next
  case (Finite_Payload v)
  then show ?thesis using finite_system_payloads_exact[of P]
    by (auto simp: finite_leaf_stated_def system_payloads_def)
next
  case (Finite_Pair a b)
  then show ?thesis by (simp add: finite_leaf_stated_def system_leaves_not_pair)
qed

section \<open>The octet map: a bijection fixing the stated payloads\<close>

text \<open>
  Every octet occurring in the sample's terms that the program does not state as a payload is paired
  with a fresh octet — the fresh address of the octets reserved so far, followed by the one octet 256
  when the moved octet is itself unformed — and the octet map swaps each pair. The reserved octets are
  the stated payloads, the octets of the stated targets and the octets of the terms, so no fresh octet
  occurs in a term, is stated, or occurs in a stated target. The map is an involution, hence a
  bijection, keeps formation, fixes every stated payload and moves every other octet of the terms to
  one that occurs in none of them.
\<close>

lemma finite_fresh_address_formed: "octets_formed (finite_fresh_address U)"
  by (simp add: finite_fresh_address_def Let_def index_address_formed)

lemma finite_fresh_extension_outside: "finite_fresh_address U @ xs |\<notin>| U"
proof -
  have "fresh_address (insert [] (fset U)) @ xs \<notin> insert [] (fset U)"
    by (rule fresh_address_extension_outside) simp
  then show ?thesis by (simp add: finite_fresh_address_exact)
qed

text \<open>
  The fresh octets share one base, the fresh address of the reserved octets, followed by the index code
  of the moved octet's position (@{const index_address}): every extension of the base is outside the
  reserved octets (@{thm [source] fresh_address_extension_outside}), and two positions' codes cancel.
  A mark ends the fresh octet of an unformed moved octet with the octet 256.
\<close>

definition octet_fresh_mark :: "octets \<Rightarrow> octets" where
  "octet_fresh_mark x=(if octets_formed x then [] else [256])"

lemma fresh_index_formed:
  "octets_formed (finite_fresh_address U @ index_address i @ octet_fresh_mark x) \<longleftrightarrow> octets_formed x"
  using finite_fresh_address_formed[of U] index_address_formed[of i]
  by (auto simp: octets_formed_def octet_fresh_mark_def)

definition octet_fresh_pairs :: "octets fset \<Rightarrow> octets list \<Rightarrow> (octets\<times>octets) list" where
  "octet_fresh_pairs U xs=(let b=finite_fresh_address U in
    map (\<lambda>(i,x). (x,b @ index_address i @ octet_fresh_mark x)) (zip [0..<length xs] xs))"

lemma octet_fresh_pairs_fst: "map fst (octet_fresh_pairs U xs)=xs"
proof -
  have "map fst (octet_fresh_pairs U xs)=map snd (zip [0..<length xs] xs)"
    by (simp add: octet_fresh_pairs_def Let_def split_def o_def)
  then show ?thesis by simp
qed

lemma octet_fresh_pairs_fresh: "y \<in> set (map snd (octet_fresh_pairs U xs)) \<Longrightarrow> y |\<notin>| U"
  by (auto simp: octet_fresh_pairs_def Let_def finite_fresh_extension_outside)

lemma octet_fresh_pairs_formed:
  "(x,f) \<in> set (octet_fresh_pairs U xs) \<Longrightarrow> octets_formed f \<longleftrightarrow> octets_formed x"
  by (auto simp: octet_fresh_pairs_def Let_def fresh_index_formed)

lemma octet_fresh_pairs_distinct:
  assumes inside: "set xs \<subseteq> fset U" and distinct: "distinct xs"
  shows "distinct (map fst (octet_fresh_pairs U xs) @ map snd (octet_fresh_pairs U xs))"
proof -
  define b where "b=finite_fresh_address U"
  let ?z="zip [0..<length xs] xs"
  let ?g="\<lambda>z. b @ index_address (fst z) @ octet_fresh_mark (snd z)"
  have snd: "map snd (octet_fresh_pairs U xs)=map ?g ?z"
    by (simp add: octet_fresh_pairs_def Let_def b_def split_def o_def)
  have indices: "inj_on fst (set ?z)" using distinct_map[of fst ?z] by simp
  have "inj_on ?g (set ?z)"
  proof (rule inj_onI)
    fix z z' assume z: "z \<in> set ?z" and z': "z' \<in> set ?z" and same: "?g z=?g z'"
    have "fst z=fst z'" using same by (simp add: index_address_cancel)
    then show "z=z'" using inj_onD[OF indices _ z z'] by blast
  qed
  moreover have "distinct ?z" by (rule distinct_zipI1) simp
  ultimately have snds: "distinct (map snd (octet_fresh_pairs U xs))" by (simp add: snd distinct_map)
  have apart: "set xs \<inter> set (map snd (octet_fresh_pairs U xs))={}"
    using inside octet_fresh_pairs_fresh[of _ U xs] by blast
  show ?thesis using distinct snds apart by (simp add: octet_fresh_pairs_fst)
qed

definition octet_swap :: "(octets\<times>octets) list \<Rightarrow> octets \<Rightarrow> octets" where
  "octet_swap ps x=(case map_of (ps @ map prod.swap ps) x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

lemma octet_swap_keys: "map fst (ps @ map prod.swap ps)=map fst ps @ map snd ps"
  by (induction ps) auto

lemma octet_swap_some:
  assumes distinct: "distinct (map fst ps @ map snd ps)"
  shows "map_of (ps @ map prod.swap ps) x=Some y \<longleftrightarrow> (x,y) \<in> set ps \<or> (y,x) \<in> set ps"
proof -
  have keys: "distinct (map fst (ps @ map prod.swap ps))" using distinct by (simp only: octet_swap_keys)
  show ?thesis by (simp only: map_of_eq_Some_iff[OF keys]) auto
qed

lemma octet_swap_involution:
  assumes distinct: "distinct (map fst ps @ map snd ps)"
  shows "octet_swap ps (octet_swap ps x)=x"
proof (cases "map_of (ps @ map prod.swap ps) x")
  case None
  then have "octet_swap ps x=x" by (simp add: octet_swap_def del: map_of_append)
  then show ?thesis by simp
next
  case (Some y)
  have reverse: "map_of (ps @ map prod.swap ps) y=Some x"
    using Some octet_swap_some[OF distinct, of x y] octet_swap_some[OF distinct, of y x] by blast
  have "octet_swap ps x=y" using Some by (simp add: octet_swap_def del: map_of_append)
  moreover have "octet_swap ps y=x" using reverse by (simp add: octet_swap_def del: map_of_append)
  ultimately show ?thesis by simp
qed

lemma octet_swap_pair:
  assumes distinct: "distinct (map fst ps @ map snd ps)" and pair: "(x,f) \<in> set ps"
  shows "octet_swap ps x=f"
  using octet_swap_some[OF distinct, of x f] pair by (simp add: octet_swap_def del: map_of_append)

lemma octet_swap_outside:
  assumes "x \<notin> set (map fst ps)" "x \<notin> set (map snd ps)"
  shows "octet_swap ps x=x"
proof -
  have "map_of (ps @ map prod.swap ps) x=None" using assms by (force simp: map_of_eq_None_iff)
  then show ?thesis by (simp add: octet_swap_def del: map_of_append)
qed

lemma octet_swap_formed:
  assumes distinct: "distinct (map fst ps @ map snd ps)"
    and formed: "\<And>x f. (x,f) \<in> set ps \<Longrightarrow> octets_formed f \<longleftrightarrow> octets_formed x"
  shows "octets_formed (octet_swap ps x) \<longleftrightarrow> octets_formed x"
proof (cases "map_of (ps @ map prod.swap ps) x")
  case None
  then show ?thesis by (simp add: octet_swap_def del: map_of_append)
next
  case (Some y)
  then have "(x,y) \<in> set ps \<or> (y,x) \<in> set ps" using octet_swap_some[OF distinct] by blast
  moreover have "octet_swap ps x=y" using Some by (simp add: octet_swap_def del: map_of_append)
  ultimately show ?thesis using formed by auto
qed

text \<open>
  The swap is asked of the index notion's red-black tree instance (@{text Tree_Map_Indexes}): the tree
  of the pairs in both directions, built once, answers the swap of every octet as the pairs do.
\<close>

definition octet_swap_table :: "(octets\<times>octets) list \<Rightarrow> (octets,octets) rbt" where
  "octet_swap_table ps=RBT.bulkload (ps @ map prod.swap ps)"

definition octet_table_swap :: "(octets,octets) rbt \<Rightarrow> octets \<Rightarrow> octets" where
  "octet_table_swap T x=(case RBT.lookup T x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

lemma octet_table_swap_exact:
  assumes distinct: "distinct (map fst ps @ map snd ps)"
  shows "octet_table_swap (octet_swap_table ps) x=octet_swap ps x"
proof -
  let ?rows="ps @ map prod.swap ps"
  have keys: "distinct (map fst ?rows)" using distinct by (simp only: octet_swap_keys)
  have found: "RBT.lookup (RBT.bulkload ?rows) x=Some y \<longleftrightarrow> map_of ?rows x=Some y" for y
    using tree_map_index.represents[OF keys, of x y] map_of_eq_Some_iff[OF keys, of x y] by simp
  have lookup: "RBT.lookup (RBT.bulkload ?rows) x=map_of ?rows x"
  proof (cases "map_of ?rows x")
    case None
    then show ?thesis using found by (cases "RBT.lookup (RBT.bulkload ?rows) x") auto
  next
    case (Some y)
    then show ?thesis using found by simp
  qed
  show ?thesis
    unfolding octet_table_swap_def octet_swap_table_def octet_swap_def lookup ..
qed

definition criticism_octet_reserved ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> octets fset" where
  "criticism_octet_reserved P ts=finite_system_payloads P |\<union>|
    ffUnion (fimage finite_target_octets (finite_system_targets P)) |\<union>| criticism_term_octets ts"

definition criticism_octet_moved ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> octets list" where
  "criticism_octet_moved P ts=sorted_list_of_fset (criticism_term_octets ts |-| finite_system_payloads P)"

definition criticism_octet_pairs ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> (octets\<times>octets) list" where
  "criticism_octet_pairs P ts=octet_fresh_pairs (criticism_octet_reserved P ts) (criticism_octet_moved P ts)"

definition criticism_octet_table ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> (octets,octets) rbt" where
  "criticism_octet_table P ts=octet_swap_table (criticism_octet_pairs P ts)"

definition criticism_octet_map ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> octets \<Rightarrow> octets" where
  "criticism_octet_map P ts=octet_table_swap (criticism_octet_table P ts)"

lemma criticism_octet_moved_set:
  "set (criticism_octet_moved P ts)=fset (criticism_term_octets ts |-| finite_system_payloads P)"
  by (simp add: criticism_octet_moved_def)

lemma criticism_octet_pairs_distinct:
  "distinct (map fst (criticism_octet_pairs P ts) @ map snd (criticism_octet_pairs P ts))"
  unfolding criticism_octet_pairs_def
  by (rule octet_fresh_pairs_distinct)
    (auto simp: criticism_octet_moved_def criticism_octet_reserved_def)

lemma criticism_octet_map_swap: "criticism_octet_map P ts=octet_swap (criticism_octet_pairs P ts)"
  by (rule ext) (simp add: criticism_octet_map_def criticism_octet_table_def
    octet_table_swap_exact[OF criticism_octet_pairs_distinct])

lemma criticism_octet_map_involution:
  "criticism_octet_map P ts (criticism_octet_map P ts x)=x"
  unfolding criticism_octet_map_swap by (rule octet_swap_involution[OF criticism_octet_pairs_distinct])

lemma criticism_octet_map_comp: "criticism_octet_map P ts \<circ> criticism_octet_map P ts=id"
  by (rule ext) (simp add: criticism_octet_map_involution)

theorem criticism_octet_map_bij: "bij (criticism_octet_map P ts)"
  by (rule o_bij[OF criticism_octet_map_comp criticism_octet_map_comp])

lemma criticism_octet_map_inj: "inj (criticism_octet_map P ts)"
  by (rule bij_is_inj[OF criticism_octet_map_bij])

theorem criticism_octet_map_formed:
  "octets_formed (criticism_octet_map P ts x) \<longleftrightarrow> octets_formed x"
  unfolding criticism_octet_map_swap
  by (rule octet_swap_formed[OF criticism_octet_pairs_distinct])
    (auto simp: criticism_octet_pairs_def dest: octet_fresh_pairs_formed)

theorem criticism_octet_map_fixes:
  assumes stated: "v |\<in>| finite_system_payloads P"
  shows "criticism_octet_map P ts v=v"
proof -
  have "v \<notin> set (map fst (criticism_octet_pairs P ts))"
    using stated by (simp add: criticism_octet_pairs_def octet_fresh_pairs_fst criticism_octet_moved_set)
  moreover have "v \<notin> set (map snd (criticism_octet_pairs P ts))"
  proof
    assume "v \<in> set (map snd (criticism_octet_pairs P ts))"
    then have "v |\<notin>| criticism_octet_reserved P ts"
      unfolding criticism_octet_pairs_def by (rule octet_fresh_pairs_fresh)
    then show False using stated by (simp add: criticism_octet_reserved_def)
  qed
  ultimately show ?thesis unfolding criticism_octet_map_swap by (rule octet_swap_outside)
qed

corollary criticism_octet_map_fixes_stated:
  "v \<in> system_payloads (decode_finite_system P) \<Longrightarrow> criticism_octet_map P ts v=v"
  using criticism_octet_map_fixes[of v P ts] finite_system_payloads_exact[of P] by simp

theorem criticism_octet_map_moves:
  assumes occurs: "v |\<in>| criticism_term_octets ts" and unstated: "v |\<notin>| finite_system_payloads P"
  shows "criticism_octet_map P ts v |\<notin>| criticism_octet_reserved P ts"
proof -
  have "v \<in> set (map fst (criticism_octet_pairs P ts))"
    using occurs unstated by (simp add: criticism_octet_pairs_def octet_fresh_pairs_fst criticism_octet_moved_set)
  then obtain f where pair: "(v,f) \<in> set (criticism_octet_pairs P ts)" by auto
  have "f |\<notin>| criticism_octet_reserved P ts"
    using pair unfolding criticism_octet_pairs_def by (intro octet_fresh_pairs_fresh) force
  then show ?thesis
    using octet_swap_pair[OF criticism_octet_pairs_distinct pair] by (simp add: criticism_octet_map_swap)
qed

corollary criticism_octet_map_moves_out:
  assumes "v |\<in>| criticism_term_octets ts" "v |\<notin>| finite_system_payloads P"
  shows "criticism_octet_map P ts v |\<notin>| criticism_term_octets ts" "criticism_octet_map P ts v\<noteq>v"
  using criticism_octet_map_moves[OF assms] assms(1) by (auto simp: criticism_octet_reserved_def)

corollary criticism_octet_map_moved_unstated:
  "criticism_octet_map P ts v\<noteq>v \<Longrightarrow> v \<notin> system_payloads (decode_finite_system P)"
  using criticism_octet_map_fixes_stated by blast

section \<open>Readdressing a target consistently with the octet map\<close>

text \<open>
  A target is readdressed by mapping every address and every attachment value of its artifact, and
  an anchor's address with them. On a finite artifact this maps its carrier, its incidence rows, its
  counted and its functional attachments; an exact artifact is readdressed through its unique finite
  representation. Its structure is the one @{const push_object} gives the artifact, its functional
  attachments are mapped on both sides and its counts are carried with them.
\<close>

definition finite_readdress :: "(octets \<Rightarrow> octets) \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_readdress h C=C\<lparr>
    finite_structure:=(finite_structure C)\<lparr>
      finite_carrier:=fimage h (finite_carrier (finite_structure C)),
      finite_incidence:=fimage (map_prod h (map_prod h h)) (finite_incidence (finite_structure C))\<rparr>,
    finite_data:=(finite_data C)\<lparr>
      finite_bag:=image_mset (map_prod h h) (finite_bag (finite_data C)),
      finite_bindings:=fimage (map_prod h h) (finite_bindings (finite_data C))\<rparr>\<rparr>"

lemma finite_readdress_involution:
  assumes involution: "h \<circ> h=id"
  shows "finite_readdress h (finite_readdress h C)=C"
proof -
  have pair: "map_prod h h \<circ> map_prod h h=id"
    and triple: "map_prod h (map_prod h h) \<circ> map_prod h (map_prod h h)=id"
    using involution by (simp_all add: map_prod.comp map_prod.id)
  show ?thesis
  proof (rule finite_structured_object.equality)
    show "finite_structure (finite_readdress h (finite_readdress h C))=finite_structure C"
      by (rule finite_rra_structure.equality)
        (simp_all add: finite_readdress_def fset.map_comp involution triple fset.map_id)
    show "finite_data (finite_readdress h (finite_readdress h C))=finite_data C"
      by (rule finite_opaque_basis.equality)
        (simp_all add: finite_readdress_def fset.map_comp multiset.map_comp pair fset.map_id multiset.map_id)
  qed (simp add: finite_readdress_def)
qed


lemma finite_readdress_formed:
  assumes formed: "finite_exact_formed C" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)"
  shows "finite_exact_formed (finite_readdress h C)"
  using formed
  by (auto simp: finite_exact_formed_def finite_object_formed_def finite_structure_formed_def
    finite_basis_formed_def finite_relation_functional_def finite_readdress_def fBall_member fimage.rep_eq
    inj_eq[OF inj] keep)

lemma finite_readdress_enumerated:
  "finite_readdress h (finite_enumerated_artifact A E B F)=finite_enumerated_artifact (map h A)
    (map (map_prod h (map_prod h h)) E) (map (map_prod h h) B) (map (map_prod h h) F)"
  by (simp add: finite_readdress_def finite_enumerated_artifact_def)

definition readdress_object :: "(octets \<Rightarrow> octets) \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact" where
  "readdress_object h R=decode_finite_object (finite_readdress h (finite_object_of R))"

lemma readdress_decoded [simp]:
  "readdress_object h (decode_finite_object C)=decode_finite_object (finite_readdress h C)"
  by (simp add: readdress_object_def)

fun readdress_target :: "(octets \<Rightarrow> octets) \<Rightarrow> exact_target \<Rightarrow> exact_target" where
  "readdress_target h (Whole_Artifact R)=Whole_Artifact (readdress_object h R)"
| "readdress_target h (Occurrence_Anchor (R,a))=Occurrence_Anchor (readdress_object h R,h a)"

fun finite_target_readdress :: "(octets \<Rightarrow> octets) \<Rightarrow> finite_exact_target \<Rightarrow> finite_exact_target" where
  "finite_target_readdress h (Finite_Whole C)=Finite_Whole (finite_readdress h C)"
| "finite_target_readdress h (Finite_Anchor C a)=Finite_Anchor (finite_readdress h C) (h a)"

lemma decode_finite_target_readdress:
  "decode_finite_target (finite_target_readdress h t)=readdress_target h (decode_finite_target t)"
  by (cases t) simp_all

lemma readdress_object_structure:
  assumes "object_formed R"
  shows "object_structure (readdress_object h R)=object_structure (push_object h R)"
proof -
  obtain C where R: "R=decode_finite_object C" using finite_object_representation[OF assms] by metis
  have map: "map_prod h (map_prod h h)=(\<lambda>(r,p,x). (h r,h p,h x))" by (auto simp: fun_eq_iff)
  show ?thesis unfolding R readdress_decoded
    by (simp add: push_object_def push_structure_def finite_readdress_def decode_finite_object_def
      decode_finite_structure_def fimage.rep_eq map)
qed

lemma readdress_object_carrier:
  assumes "object_formed R"
  shows "rra_carrier (object_structure (readdress_object h R))=h ` rra_carrier (object_structure R)"
  using readdress_object_structure[OF assms, of h] by (simp add: push_object_def)

lemma readdress_object_bindings:
  assumes "object_formed R"
  shows "functional_bindings (object_data (readdress_object h R))=
    map_prod h h ` functional_bindings (object_data R)"
proof -
  obtain C where R: "R=decode_finite_object C" using finite_object_representation[OF assms] by metis
  show ?thesis unfolding R readdress_decoded
    by (simp add: finite_readdress_def decode_finite_object_def decode_finite_basis_def fimage.rep_eq)
qed

lemma count_image_mset_injective: "inj f \<Longrightarrow> count (image_mset f M) (f x)=count M x"
  by (induction M) (auto simp: inj_eq)

lemma readdress_object_counts:
  assumes formed: "object_formed R" and inj: "inj h"
  shows "bag_count (object_data (readdress_object h R)) (h a,h v)=bag_count (object_data R) (a,v)"
proof -
  obtain C where R: "R=decode_finite_object C" using finite_object_representation[OF formed] by metis
  have pairs: "inj (map_prod h h)" using map_prod_inj_on[OF inj inj] by simp
  show ?thesis unfolding R readdress_decoded
    using count_image_mset_injective[OF pairs, of "finite_bag (finite_data C)" "(a,v)"]
    by (simp add: finite_readdress_def decode_finite_object_def decode_finite_basis_def)
qed

lemma readdress_object_formed:
  assumes formed: "exact_formed R" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)"
  shows "exact_formed (readdress_object h R)"
proof -
  have object: "object_formed R" using formed by (simp add: exact_formed_def)
  obtain C where R: "R=decode_finite_object C" using finite_object_representation[OF object] by metis
  have "finite_exact_formed C" using formed by (simp add: R finite_exact_formed_correct)
  then have "finite_exact_formed (finite_readdress h C)" by (rule finite_readdress_formed[OF _ inj keep])
  then show ?thesis by (simp add: R finite_exact_formed_correct)
qed

lemma readdress_target_formed:
  assumes formed: "target_formed t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)"
  shows "target_formed (readdress_target h t)"
proof (cases t)
  case (Whole_Artifact R)
  then show ?thesis using formed readdress_object_formed[OF _ inj keep] by simp
next
  case (Occurrence_Anchor z)
  obtain R a where z: "z=(R,a)" by (cases z)
  have R: "exact_formed R" and a: "a \<in> rra_carrier (object_structure R)"
    using formed by (simp_all add: Occurrence_Anchor z anchor_formed_def)
  have object: "object_formed R" using R by (simp add: exact_formed_def)
  show ?thesis
    using readdress_object_formed[OF R inj keep] a readdress_object_carrier[OF object, of h]
    by (simp add: Occurrence_Anchor z anchor_formed_def)
qed

section \<open>The leaf map the octet map induces\<close>

text \<open>
  The image of a leaf maps a payload by the octet map and readdresses a target. The leaf map keeps
  every stated leaf, and every leaf whose image is stated; it takes every other leaf to its image.
  It fixes the stated leaves by construction, and it is formed when the octet map is injective and
  keeps formation. The finite leaf map is the same map on finite terms, and it decodes to it.
\<close>

fun octet_leaf_image :: "(octets \<Rightarrow> octets) \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "octet_leaf_image h (Target_Term t)=Target_Term (readdress_target h t)"
| "octet_leaf_image h (Payload_Term v)=Payload_Term (h v)"
| "octet_leaf_image h (Pair_Term x y)=Pair_Term x y"

definition octet_leaf_map :: "(octets \<Rightarrow> octets) \<Rightarrow> factor_term set \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "octet_leaf_map h K x=(if x \<in> K \<or> octet_leaf_image h x \<in> K then x else octet_leaf_image h x)"

lemma octet_leaf_map_fixes: "x \<in> K \<Longrightarrow> octet_leaf_map h K x=x"
  by (simp add: octet_leaf_map_def)

lemma octet_leaf_map_formed:
  assumes inj: "inj h" and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)"
  shows "leaf_map_formed (octet_leaf_map h K)"
  using readdress_target_formed[OF _ inj keep] keep
  by (auto simp: leaf_map_formed_def octet_leaf_map_def)

lemma octet_leaf_map_payload:
  assumes inj: "inj h" and stated: "\<And>v. Payload_Term v \<in> K \<Longrightarrow> h v=v"
  shows "octet_leaf_map h K (Payload_Term v)=Payload_Term (h v)"
proof (cases "Payload_Term v \<in> K")
  case True
  then show ?thesis using stated by (simp add: octet_leaf_map_def)
next
  case False
  have "Payload_Term (h v) \<notin> K"
  proof
    assume member: "Payload_Term (h v) \<in> K"
    then have "h (h v)=h v" by (rule stated)
    then have "h v=v" using inj by (simp add: inj_eq)
    then show False using member False by simp
  qed
  then show ?thesis using False by (simp add: octet_leaf_map_def)
qed

lemma octet_leaf_map_self_contained:
  assumes contained: "self_contained_term t" and inj: "inj h"
    and stated: "\<And>v. Payload_Term v \<in> K \<Longrightarrow> h v=v"
  shows "map_term_leaves (octet_leaf_map h K) t=map_term_leaves (octet_leaf_image h) t"
  using contained by (induction t) (simp_all add: octet_leaf_map_payload[OF inj stated])

fun finite_leaf_image :: "(octets \<Rightarrow> octets) \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term" where
  "finite_leaf_image h (Finite_Target t)=Finite_Target (finite_target_readdress h t)"
| "finite_leaf_image h (Finite_Payload v)=Finite_Payload (h v)"
| "finite_leaf_image h (Finite_Pair x y)=Finite_Pair x y"

definition finite_octet_leaf_map ::
    "(octets \<Rightarrow> octets) \<Rightarrow> (finite_factor_term \<Rightarrow> bool) \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term" where
  "finite_octet_leaf_map h k x=(if k x \<or> k (finite_leaf_image h x) then x else finite_leaf_image h x)"

fun finite_map_term_leaves ::
    "(finite_factor_term \<Rightarrow> finite_factor_term) \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term" where
  "finite_map_term_leaves f (Finite_Target t)=f (Finite_Target t)"
| "finite_map_term_leaves f (Finite_Payload v)=f (Finite_Payload v)"
| "finite_map_term_leaves f (Finite_Pair x y)=Finite_Pair (finite_map_term_leaves f x) (finite_map_term_leaves f y)"

lemma decode_finite_leaf_image:
  "decode_finite_term (finite_leaf_image h y)=octet_leaf_image h (decode_finite_term y)"
  by (cases y) (simp_all add: decode_finite_target_readdress)

lemma decode_finite_octet_leaf_map:
  assumes stated: "\<And>y. k y \<longleftrightarrow> decode_finite_term y \<in> K"
  shows "decode_finite_term (finite_octet_leaf_map h k y)=octet_leaf_map h K (decode_finite_term y)"
  unfolding finite_octet_leaf_map_def octet_leaf_map_def by (simp add: stated decode_finite_leaf_image)

lemma decode_finite_map_term_leaves:
  assumes "\<And>y. decode_finite_term (f y)=g (decode_finite_term y)"
  shows "decode_finite_term (finite_map_term_leaves f t)=map_term_leaves g (decode_finite_term t)"
  by (induction t) (simp_all add: assms)

lemma finite_leaf_image_involution:
  assumes involution: "h \<circ> h=id"
  shows "finite_leaf_image h (finite_leaf_image h y)=y"
proof -
  have point: "h (h x)=x" for x using involution by (metis comp_apply id_apply)
  show ?thesis
  proof (cases y)
    case (Finite_Target t)
    then show ?thesis by (cases t) (simp_all add: finite_readdress_involution[OF involution] point)
  qed (simp_all add: point)
qed

lemma finite_octet_leaf_map_leaf_involution:
  assumes "\<And>y. finite_leaf_image h (finite_leaf_image h y)=y"
  shows "finite_octet_leaf_map h k (finite_octet_leaf_map h k y)=y"
  using assms by (auto simp: finite_octet_leaf_map_def)

lemma finite_octet_leaf_map_involution:
  assumes involution: "h \<circ> h=id"
  shows "finite_map_term_leaves (finite_octet_leaf_map h k) (finite_map_term_leaves (finite_octet_leaf_map h k) t)=t"
proof (induction t)
  case (Finite_Target t)
  have "\<exists>t'. finite_octet_leaf_map h k (Finite_Target t)=Finite_Target t'"
    by (cases "k (Finite_Target t) \<or> k (finite_leaf_image h (Finite_Target t))")
      (auto simp: finite_octet_leaf_map_def)
  then obtain t' where image: "finite_octet_leaf_map h k (Finite_Target t)=Finite_Target t'" by blast
  have "finite_octet_leaf_map h k (finite_octet_leaf_map h k (Finite_Target t))=Finite_Target t"
    by (rule finite_octet_leaf_map_leaf_involution[OF finite_leaf_image_involution[OF involution]])
  then show ?case using image by simp
next
  case (Finite_Payload v)
  have "\<exists>v'. finite_octet_leaf_map h k (Finite_Payload v)=Finite_Payload v'"
    by (cases "k (Finite_Payload v) \<or> k (finite_leaf_image h (Finite_Payload v))")
      (auto simp: finite_octet_leaf_map_def)
  then obtain v' where image: "finite_octet_leaf_map h k (Finite_Payload v)=Finite_Payload v'" by blast
  have "finite_octet_leaf_map h k (finite_octet_leaf_map h k (Finite_Payload v))=Finite_Payload v"
    by (rule finite_octet_leaf_map_leaf_involution[OF finite_leaf_image_involution[OF involution]])
  then show ?case using image by simp
qed simp

section \<open>The sample and its leaf map\<close>

text \<open>
  The octet sample of a finite program at a list of argument terms pairs each term with its image
  under the finite leaf map of the octet map, the stated leaves being the program's. The abstract
  leaf map is the octet map's leaf map at the stated leaves of the decoded program.
\<close>

definition criticism_octet_sample ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term" where
  "criticism_octet_sample P ts=(let h=criticism_octet_map P ts;
    k=finite_leaf_stated_in (finite_system_payloads P) (finite_system_targets P) in
      finite_map_term_leaves (finite_octet_leaf_map h k))"

lemma criticism_octet_sample_eq:
  "criticism_octet_sample P ts=finite_map_term_leaves (finite_octet_leaf_map (criticism_octet_map P ts) (finite_leaf_stated P))"
  by (simp add: criticism_octet_sample_def finite_leaf_stated_def Let_def)

definition octet_sample_pairs ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list" where
  "octet_sample_pairs P ts=(let s=criticism_octet_sample P ts in map (\<lambda>t. (t,s t)) ts)"

definition criticism_octet_leaf_map ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term list \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "criticism_octet_leaf_map P ts=octet_leaf_map (criticism_octet_map P ts) (system_leaves (decode_finite_system P))"

lemma criticism_octet_sample_involution:
  "criticism_octet_sample P ts (criticism_octet_sample P ts t)=t"
  unfolding criticism_octet_sample_eq by (rule finite_octet_leaf_map_involution[OF criticism_octet_map_comp])

lemma decode_criticism_octet_sample:
  "decode_finite_term (criticism_octet_sample P ts t)=
    map_term_leaves (criticism_octet_leaf_map P ts) (decode_finite_term t)"
  unfolding criticism_octet_sample_eq criticism_octet_leaf_map_def
  by (rule decode_finite_map_term_leaves, rule decode_finite_octet_leaf_map, rule finite_leaf_stated_exact)

theorem criticism_octet_leaf_map_fixes:
  "x \<in> system_leaves (decode_finite_system P) \<Longrightarrow> criticism_octet_leaf_map P ts x=x"
  by (simp add: criticism_octet_leaf_map_def octet_leaf_map_fixes)

theorem criticism_octet_leaf_map_formed: "leaf_map_formed (criticism_octet_leaf_map P ts)"
  unfolding criticism_octet_leaf_map_def
  by (rule octet_leaf_map_formed[OF criticism_octet_map_inj]) (simp add: criticism_octet_map_formed)

lemma criticism_octet_stated_payloads:
  "Payload_Term v \<in> system_leaves (decode_finite_system P) \<Longrightarrow> criticism_octet_map P ts v=v"
  by (rule criticism_octet_map_fixes_stated) (simp add: system_payloads_def)

section \<open>On presented data the leaf map is the readdressing\<close>

text \<open>
  A term presenting self-contained data carries no target, so the leaf map maps each of its payloads
  by the octet map. Where the octet map keeps the empty payload, which ends every data list, the
  presentation of an artifact's rows is mapped to the presentation of the readdressed artifact's rows:
  every presented address and every presented attachment value is mapped as the readdressing maps
  the artifact.
\<close>

lemma map_data_list_term:
  assumes "g (Payload_Term [])=Payload_Term []"
  shows "map_term_leaves g (data_list_term ts)=data_list_term (map (map_term_leaves g) ts)"
  by (induction ts) (simp_all add: assms)

lemma map_address_pair_data:
  "map_term_leaves (octet_leaf_image h) (address_pair_data z)=address_pair_data (map_prod h h z)"
  by (cases z) (simp add: address_pair_data_def)

lemma map_incidence_data:
  "map_term_leaves (octet_leaf_image h) (incidence_data z)=incidence_data (map_prod h (map_prod h h) z)"
  by (cases z) (simp add: incidence_data_def address_pair_data_def)

theorem readdress_artifact_value:
  assumes present: "artifact_value_presents R t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)" and empty: "h []=[]"
  shows "artifact_value_presents (readdress_object h R) (map_term_leaves (octet_leaf_image h) t)"
proof -
  obtain A E B F where enumeration: "artifact_enumeration R A E B F" and t: "t=artifact_data_term A E B F"
    using present by (auto simp: artifact_value_presents_def)
  have R: "R=decode_finite_object (finite_enumerated_artifact A E B F)"
    using enumeration by (simp add: artifact_enumeration_def)
  let ?A="map h A" and ?E="map (map_prod h (map_prod h h)) E" and ?B="map (map_prod h h) B"
    and ?F="map (map_prod h h) F"
  have readdressed: "readdress_object h R=enumerated_artifact ?A ?E ?B ?F"
    unfolding R readdress_decoded finite_readdress_enumerated by (rule decode_finite_enumerated_artifact)
  have pairs: "inj (map_prod h h)" using map_prod_inj_on[OF inj inj] by simp
  have triples: "inj (map_prod h (map_prod h h))" using map_prod_inj_on[OF inj pairs] by simp
  have source: "exact_formed R" using enumeration unfolding artifact_enumeration_def by blast
  have formed: "exact_formed (readdress_object h R)" by (rule readdress_object_formed[OF source inj keep])
  have enumerated: "artifact_enumeration (readdress_object h R) ?A ?E ?B ?F"
    using enumeration formed readdressed inj pairs triples
    by (simp add: artifact_enumeration_def distinct_map inj_on_subset[OF _ subset_UNIV])
  have mapped: "map_term_leaves (octet_leaf_image h) t=artifact_data_term ?A ?E ?B ?F"
    by (simp add: t artifact_data_term_def map_data_list_term empty comp_def map_incidence_data
      map_address_pair_data)
  show ?thesis using enumerated by (simp add: mapped artifact_value_presents_data)
qed

lemma map_natural_data_term:
  "h []=[] \<Longrightarrow> map_term_leaves (octet_leaf_image h) (natural_data_term n)=natural_data_term n"
  by (induction n) simp_all

lemma map_use_data_term:
  assumes empty: "h []=[]"
  shows "map_term_leaves (octet_leaf_image h) (use_data_term u)=use_data_term u"
proof (cases u)
  case None
  then show ?thesis using empty by simp
next
  case (Some a)
  have end_: "octet_leaf_image h (Payload_Term [])=Payload_Term []" using empty by simp
  show ?thesis
    using empty by (simp add: Some map_data_list_term[of "octet_leaf_image h", OF end_] comp_def
      map_natural_data_term)
qed

lemma map_site_data_term:
  "h []=[] \<Longrightarrow> map_term_leaves (octet_leaf_image h) (site_data_term u r)=site_data_term u (h r)"
  by (simp add: site_data_term_def map_use_data_term)

lemma map_binding_data:
  "h []=[] \<Longrightarrow> map_term_leaves (octet_leaf_image h) (binding_data ((u,k),v))=binding_data ((u,h k),v)"
  by (simp add: binding_data_def map_use_data_term)

theorem readdress_environment_entry:
  assumes present: "environment_artifact_entry_presents (u,R) t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)" and empty: "h []=[]"
  shows "environment_artifact_entry_presents (u,readdress_object h R) (map_term_leaves (octet_leaf_image h) t)"
proof -
  obtain v where v: "artifact_value_presents R v" and t: "t=Pair_Term (use_data_term u) v"
    using present by (auto simp: environment_artifact_entry_presents_def)
  show ?thesis using readdress_artifact_value[OF v inj keep empty]
    by (auto simp: environment_artifact_entry_presents_def t map_use_data_term[of h, OF empty])
qed

theorem criticism_octet_artifact_value:
  assumes present: "artifact_value_presents R t" and empty: "criticism_octet_map P ts []=[]"
  shows "artifact_value_presents (readdress_object (criticism_octet_map P ts) R)
    (map_term_leaves (criticism_octet_leaf_map P ts) t)"
proof -
  have contained: "self_contained_term t" using artifact_value_presents_formed[OF present] by simp
  have "map_term_leaves (criticism_octet_leaf_map P ts) t=map_term_leaves (octet_leaf_image (criticism_octet_map P ts)) t"
    unfolding criticism_octet_leaf_map_def
    by (rule octet_leaf_map_self_contained[OF contained criticism_octet_map_inj criticism_octet_stated_payloads])
  moreover have keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (criticism_octet_map P ts x)"
    by (simp add: criticism_octet_map_formed)
  ultimately show ?thesis
    using readdress_artifact_value[OF present criticism_octet_map_inj keep empty] by simp
qed

section \<open>A readdressed environment and its presented values\<close>

text \<open>
  An environment is readdressed by readdressing each of its artifacts and mapping each binding's slot,
  its uses unchanged. It stays formed under an injective octet map keeping formation, and where the map
  keeps the empty payload every presentation of the environment, of a site of it and of a program entry
  of it is mapped by the leaf image to a presentation of the readdressed environment at the readdressed
  site: the collections are lifted row by row, each subject mapped injectively.
\<close>

definition readdress_environment :: "(octets \<Rightarrow> octets) \<Rightarrow> 'u artifact_environment \<Rightarrow> 'u artifact_environment" where
  "readdress_environment h E=\<lparr>environment_artifacts=(\<lambda>(u,R). (u,readdress_object h R)) ` environment_artifacts E,
    environment_bindings=(\<lambda>((u,k),v). ((u,h k),v)) ` environment_bindings E\<rparr>"

lemma readdress_environment_artifact:
  "artifact_at (readdress_environment h E) u S \<longleftrightarrow> (\<exists>R. artifact_at E u R \<and> S=readdress_object h R)"
  by (auto simp: readdress_environment_def artifact_at_def)

lemma readdress_environment_binding:
  "binds_slot (readdress_environment h E) u k' v \<longleftrightarrow> (\<exists>k. binds_slot E u k v \<and> k'=h k)"
proof
  assume "binds_slot (readdress_environment h E) u k' v"
  then show "\<exists>k. binds_slot E u k v \<and> k'=h k" by (auto simp: readdress_environment_def binds_slot_def)
next
  assume "\<exists>k. binds_slot E u k v \<and> k'=h k"
  then obtain k where bound: "((u,k),v) \<in> environment_bindings E" and k': "k'=h k"
    by (auto simp: binds_slot_def)
  show "binds_slot (readdress_environment h E) u k' v"
    unfolding readdress_environment_def binds_slot_def using bound
    by (auto simp: k' intro!: rev_image_eqI[of "((u,k),v)"])
qed

lemma readdress_environment_uses: "environment_uses (readdress_environment h E)=environment_uses E"
  by (force simp: readdress_environment_def environment_uses_def rel_dom_def)

theorem readdress_environment_formed:
  assumes formed: "environment_formed E" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)"
  shows "environment_formed (readdress_environment h E)"
proof -
  let ?F="readdress_environment h E"
  have finite: "finite (environment_artifacts E)" "finite (environment_bindings E)"
    and sv: "single_valued (environment_artifacts E)" "single_valued (environment_bindings E)"
    using formed unfolding environment_formed_def by blast+
  have artifacts: "exact_formed R" if "artifact_at E u R" for u R
    using formed that unfolding environment_formed_def by blast
  have slots: "(\<exists>R. artifact_at E u R \<and> k \<in> rra_carrier (object_structure R)) \<and> v \<in> environment_uses E"
    if "binds_slot E u k v" for u k v
    using formed that unfolding environment_formed_def by blast
  have finite': "finite (environment_artifacts ?F)" "finite (environment_bindings ?F)"
    using finite by (simp_all add: readdress_environment_def)
  have sv_artifacts: "single_valued (environment_artifacts ?F)"
    using sv(1) by (auto simp: readdress_environment_def single_valued_def)
  have sv_bindings: "single_valued (environment_bindings ?F)"
    using sv(2) inj by (auto simp: readdress_environment_def single_valued_def inj_eq)
  have formed': "exact_formed S" if "artifact_at ?F u S" for u S
    using that artifacts readdress_object_formed[OF _ inj keep] by (auto simp: readdress_environment_artifact)
  have slots': "(\<exists>S. artifact_at ?F u S \<and> k' \<in> rra_carrier (object_structure S)) \<and> v \<in> environment_uses ?F"
    if "binds_slot ?F u k' v" for u k' v
  proof -
    have "\<exists>k. binds_slot E u k v \<and> k'=h k" using that by (simp only: readdress_environment_binding)
    then obtain k where bound: "binds_slot E u k v" and k': "k'=h k" by blast
    obtain R where R: "artifact_at E u R" and k: "k \<in> rra_carrier (object_structure R)"
      and v: "v \<in> environment_uses E"
      using slots[OF bound] by blast
    have object: "object_formed R" using artifacts[OF R] by (simp add: exact_formed_def)
    have "artifact_at ?F u (readdress_object h R)" using R by (auto simp: readdress_environment_artifact)
    moreover have "k' \<in> rra_carrier (object_structure (readdress_object h R))"
      using k by (simp add: k' readdress_object_carrier[OF object])
    ultimately show ?thesis using v by (auto simp: readdress_environment_uses)
  qed
  show ?thesis
    unfolding environment_formed_def using finite' sv_artifacts sv_bindings formed' slots' by blast
qed

lemma readdress_environment_positions:
  assumes formed: "environment_formed E" and position: "(u,r) \<in> environment_positions E"
  shows "(u,h r) \<in> environment_positions (readdress_environment h E)"
proof -
  obtain R where R: "artifact_at E u R" and r: "r \<in> rra_carrier (object_structure R)"
    using position by (auto simp: environment_positions_def artifact_at_def)
  have object: "object_formed R" using formed R by (auto simp: environment_formed_def exact_formed_def)
  have "artifact_at (readdress_environment h E) u (readdress_object h R)"
    using R by (auto simp: readdress_environment_artifact)
  then show ?thesis unfolding environment_positions_def artifact_at_def
    using r by (auto simp: readdress_object_carrier[OF object] intro!: bexI[of _ "(u,readdress_object h R)"])
qed

lemma data_collection_presents_leaf_map:
  assumes present: "data_collection_presents read A t" and injective: "inj_on f A"
    and changed: "\<And>x y. x \<in> A \<Longrightarrow> read x y \<Longrightarrow> read' (f x) (map_term_leaves g y)"
    and empty: "g (Payload_Term [])=Payload_Term []"
  shows "data_collection_presents read' (f ` A) (map_term_leaves g t)"
proof -
  obtain xs ts where distinct: "distinct xs" and members: "set xs=A" and read: "list_all2 read xs ts"
    and t: "t=data_list_term ts"
    using present by (auto simp: data_collection_presents_def)
  have "list_all2 (\<lambda>x y. read' (f x) (map_term_leaves g y)) xs ts"
    using read unfolding list_all2_conv_all_nth by (auto intro: changed simp: members[symmetric])
  then have mapped: "list_all2 read' (map f xs) (map (map_term_leaves g) ts)"
    by (simp add: list_all2_map1 list_all2_map2)
  have "distinct (map f xs)" using distinct injective members by (simp add: distinct_map)
  then show ?thesis unfolding data_collection_presents_def
    using mapped members
    by (intro exI[of _ "map f xs"] exI[of _ "map (map_term_leaves g) ts"])
      (simp add: t map_data_list_term[of g, OF empty])
qed

theorem readdress_environment_value:
  assumes present: "environment_value_presents E t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)" and empty: "h []=[]"
  shows "environment_value_presents (readdress_environment h E) (map_term_leaves (octet_leaf_image h) t)"
proof -
  obtain a b where formed: "environment_formed E"
    and artifacts: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    and bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E) b"
    and t: "t=Pair_Term a b"
    using present by (auto simp: environment_value_presents_def)
  have end_: "octet_leaf_image h (Payload_Term [])=Payload_Term []" using empty by simp
  have sv: "single_valued (environment_artifacts E)" using formed by (simp add: environment_formed_def)
  have artifacts_inj: "inj_on (\<lambda>(u,R). (u,readdress_object h R)) (environment_artifacts E)"
    using sv by (auto simp: inj_on_def single_valued_def)
  have bindings_inj: "inj_on (\<lambda>((u,k),v). ((u,h k),v)) (environment_bindings E)"
  proof (rule inj_onI)
    fix z z' assume same: "(\<lambda>((u,k),v). ((u,h k),v)) z=(\<lambda>((u,k),v). ((u,h k),v)) z'"
    obtain u k v where z: "z=((u,k),v)" by (metis prod.collapse)
    obtain u' k' v' where z': "z'=((u',k'),v')" by (metis prod.collapse)
    have parts: "u=u'" "h k=h k'" "v=v'" using same by (simp_all add: z z')
    have "k=k'" by (rule injD[OF inj parts(2)])
    then show "z=z'" using parts by (simp add: z z')
  qed
  have entry: "environment_artifact_entry_presents ((\<lambda>(u,R). (u,readdress_object h R)) z)
      (map_term_leaves (octet_leaf_image h) y)"
    if "z \<in> environment_artifacts E" "environment_artifact_entry_presents z y" for z y
  proof -
    obtain u R where z: "z=(u,R)" by (cases z)
    show ?thesis using readdress_environment_entry[OF _ inj keep empty, of u R y] that by (simp add: z)
  qed
  have binding: "map_term_leaves (octet_leaf_image h) y=binding_data ((\<lambda>((u,k),v). ((u,h k),v)) z)"
    if "z \<in> environment_bindings E" "y=binding_data z" for z y
  proof -
    obtain q v where zq: "z=(q,v)" by (cases z)
    obtain u k where q: "q=(u,k)" by (cases q)
    show ?thesis using that empty by (simp add: zq q map_binding_data)
  qed
  have artifacts': "data_collection_presents environment_artifact_entry_presents
      ((\<lambda>(u,R). (u,readdress_object h R)) ` environment_artifacts E) (map_term_leaves (octet_leaf_image h) a)"
    by (rule data_collection_presents_leaf_map[where read'=environment_artifact_entry_presents
      and g="octet_leaf_image h", OF artifacts artifacts_inj entry end_])
  have bindings': "data_collection_presents (\<lambda>z v. v=binding_data z)
      ((\<lambda>((u,k),v). ((u,h k),v)) ` environment_bindings E) (map_term_leaves (octet_leaf_image h) b)"
    by (rule data_collection_presents_leaf_map[where read'="\<lambda>z v. v=binding_data z"
      and g="octet_leaf_image h", OF bindings bindings_inj binding end_])
  show ?thesis unfolding environment_value_presents_def
    using readdress_environment_formed[OF formed inj keep] artifacts' bindings'
    by (simp add: readdress_environment_def t)
qed

theorem readdress_site_value:
  assumes present: "site_value_presents E u r t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)" and empty: "h []=[]"
  shows "site_value_presents (readdress_environment h E) u (h r) (map_term_leaves (octet_leaf_image h) t)"
proof -
  obtain e where position: "(u,r) \<in> environment_positions E" and e: "environment_value_presents E e"
    and t: "t=Pair_Term e (site_data_term u r)"
    using present by (auto simp: site_value_presents_def)
  have formed: "environment_formed E" using environment_value_presents_formed[OF e] by simp
  show ?thesis unfolding site_value_presents_def
    using readdress_environment_positions[OF formed position] readdress_environment_value[OF e inj keep empty]
    by (simp add: t map_site_data_term[of h, OF empty])
qed

theorem readdress_program_entry_value:
  assumes present: "program_entry_value_presents E u r d t" and inj: "inj h"
    and keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (h x)" and empty: "h []=[]"
  shows "program_entry_value_presents (readdress_environment h E) u (h r) (fst d,h (snd d))
    (map_term_leaves (octet_leaf_image h) t)"
proof -
  obtain s where position: "d \<in> environment_positions E" and s: "site_value_presents E u r s"
    and t: "t=Pair_Term s (site_data_term (fst d) (snd d))"
    using present by (auto simp: program_entry_value_presents_def)
  obtain e where "environment_value_presents E e" using s by (auto simp: site_value_presents_def)
  then have formed: "environment_formed E" using environment_value_presents_formed by blast
  have "(fst d,h (snd d)) \<in> environment_positions (readdress_environment h E)"
    using readdress_environment_positions[OF formed, of "fst d" "snd d" h] position by simp
  then show ?thesis unfolding program_entry_value_presents_def
    using readdress_site_value[OF s inj keep empty] by (simp add: t map_site_data_term[of h, OF empty])
qed


text \<open>At the sample: the leaf map of the octet map is the readdressing on site and program entry values.\<close>

corollary criticism_octet_site_value:
  assumes present: "site_value_presents E u r t" and empty: "criticism_octet_map P ts []=[]"
  shows "site_value_presents (readdress_environment (criticism_octet_map P ts) E) u (criticism_octet_map P ts r)
    (map_term_leaves (criticism_octet_leaf_map P ts) t)"
proof -
  obtain e where e: "environment_value_presents E e" and t: "t=Pair_Term e (site_data_term u r)"
    using present by (auto simp: site_value_presents_def)
  have contained: "self_contained_term t"
    using environment_value_presents_formed[OF e] site_data_term_self_contained[of u r] by (simp add: t)
  have keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (criticism_octet_map P ts x)"
    by (simp add: criticism_octet_map_formed)
  have "map_term_leaves (criticism_octet_leaf_map P ts) t=map_term_leaves (octet_leaf_image (criticism_octet_map P ts)) t"
    unfolding criticism_octet_leaf_map_def
    by (rule octet_leaf_map_self_contained[OF contained criticism_octet_map_inj criticism_octet_stated_payloads])
  then show ?thesis using readdress_site_value[OF present criticism_octet_map_inj keep empty] by simp
qed

corollary criticism_octet_program_entry_value:
  assumes present: "program_entry_value_presents E u r d t" and empty: "criticism_octet_map P ts []=[]"
  shows "program_entry_value_presents (readdress_environment (criticism_octet_map P ts) E) u (criticism_octet_map P ts r)
    (fst d,criticism_octet_map P ts (snd d)) (map_term_leaves (criticism_octet_leaf_map P ts) t)"
proof -
  obtain s where s: "site_value_presents E u r s" and t: "t=Pair_Term s (site_data_term (fst d) (snd d))"
    using present by (auto simp: program_entry_value_presents_def)
  obtain e where e: "environment_value_presents E e" and st: "s=Pair_Term e (site_data_term u r)"
    using s by (auto simp: site_value_presents_def)
  have contained: "self_contained_term t"
    using environment_value_presents_formed[OF e] site_data_term_self_contained by (simp add: t st)
  have keep: "\<And>x. octets_formed x \<Longrightarrow> octets_formed (criticism_octet_map P ts x)"
    by (simp add: criticism_octet_map_formed)
  have "map_term_leaves (criticism_octet_leaf_map P ts) t=map_term_leaves (octet_leaf_image (criticism_octet_map P ts)) t"
    unfolding criticism_octet_leaf_map_def
    by (rule octet_leaf_map_self_contained[OF contained criticism_octet_map_inj criticism_octet_stated_payloads])
  then show ?thesis using readdress_program_entry_value[OF present criticism_octet_map_inj keep empty] by simp
qed

section \<open>The material premises an entry's closure reaches\<close>

text \<open>
  An entry's closure is the definitions its clauses reach through their calls; the material premises
  of the clauses at those definitions are listed from the finite program. An empty list is exactly
  observation-freeness of the program rooted at the entry.
\<close>

definition finite_entry_materials ::
    "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> (('d\<times>'c)\<times>('a,'s,'d) finite_factor_schema) fset" where
  "finite_entry_materials P d=ffilter (\<lambda>((e,c),S). finite_edge_reaches (finite_dependency_edges P) d e \<and>
    finite_schema_materials S\<noteq>{||}) (finite_system_clauses P)"

theorem finite_entry_materials_exact:
  "finite_entry_materials P d={||} \<longleftrightarrow> system_observation_free (rooted_system (decode_finite_system P) {d})"
proof -
  have reach: "e \<in> system_definition_closure (decode_finite_system P) {d} \<longleftrightarrow>
      finite_edge_reaches (finite_dependency_edges P) d e" for e
    by (simp add: system_definition_closure_def finite_edge_reaches_correct finite_dependency_edges_correct)
  have materials: "schema_material_premises (decode_finite_schema S)={} \<longleftrightarrow> finite_schema_materials S={||}" for S
    by (auto simp: decode_finite_schema_def map_relation_values_def fset_eq_iff)
  have empty: "finite_entry_materials P d={||} \<longleftrightarrow>
      (\<forall>e c S. ((e,c),S) \<in> fset (finite_system_clauses P) \<longrightarrow>
        finite_edge_reaches (finite_dependency_edges P) d e \<longrightarrow> finite_schema_materials S={||})"
    by (auto simp: finite_entry_materials_def fset_eq_iff)
  have decoded: "system_clauses (decode_finite_system P)=
      map_relation_values decode_finite_schema (fset (finite_system_clauses P))"
    by (simp add: decode_finite_system_def)
  have clauses: "((e,c),S) \<in> system_clauses (rooted_system (decode_finite_system P) {d}) \<longleftrightarrow>
      (\<exists>S'. ((e,c),S') \<in> fset (finite_system_clauses P) \<and> S=decode_finite_schema S' \<and>
        finite_edge_reaches (finite_dependency_edges P) d e)" for e c S
    by (auto simp: rooted_system_def decoded reach[symmetric])
  have "system_observation_free (rooted_system (decode_finite_system P) {d}) \<longleftrightarrow>
      (\<forall>e c S'. ((e,c),S') \<in> fset (finite_system_clauses P) \<longrightarrow>
        finite_edge_reaches (finite_dependency_edges P) d e \<longrightarrow>
        schema_material_premises (decode_finite_schema S')={})"
    unfolding system_observation_free_def clauses by blast
  then show ?thesis by (simp only: empty materials)
qed

section \<open>The leaf argument's instance: an observation-free closure records no row\<close>

text \<open>
  The sample evaluates the program's entries natively at both sides of every pair. By the leaf
  argument an entry whose closure holds no material premise holds at a term exactly when it holds at
  its image, the leaf map fixing every leaf the program states and keeping formation; so no pair of
  the sample is recorded at it. A recorded row therefore exhibits an entry whose closure holds a
  material premise, which reads an octet the program does not state — part (g) of the octet audit —
  and the material premises its closure reaches are listed with the row.
\<close>

theorem octet_sample_no_row:
  assumes formed: "schema_system_formed (decode_finite_system P)"
    and free: "finite_entry_materials P d={||}"
    and table: "criticism_table P ds (octet_sample_pairs P ts)=Some A"
  shows "(c,c',d,w) |\<notin>| criticism_record ds (octet_sample_pairs P ts) A"
proof
  assume row: "(c,c',d,w) |\<in>| criticism_record ds (octet_sample_pairs P ts) A"
  let ?P="decode_finite_system P" and ?L="criticism_octet_leaf_map P ts" and ?s="criticism_octet_sample P ts"
  have paired: "criticism_paired (octet_sample_pairs P ts) c c'"
    and holds: "(d,decode_finite_term c) \<in> positive_meaning ?P"
    and fails: "(d,decode_finite_term c') \<notin> positive_meaning ?P"
    using row by (simp_all add: criticism_record_meaning[OF table])
  have image: "c'=?s c"
  proof -
    from paired consider (forward) "(c,c') \<in> set (octet_sample_pairs P ts)"
      | (backward) "(c',c) \<in> set (octet_sample_pairs P ts)"
      by (auto simp: criticism_paired_def)
    then show ?thesis
    proof cases
      case forward
      then show ?thesis by (auto simp: octet_sample_pairs_def Let_def)
    next
      case backward
      then have "c=?s c'" by (auto simp: octet_sample_pairs_def Let_def)
      then show ?thesis by (simp only: criticism_octet_sample_involution)
    qed
  qed
  let ?R="rooted_system ?P {d}"
  have observation_free: "system_observation_free ?R" using finite_entry_materials_exact[of P d] free by simp
  have root: "d \<in> system_definition_closure ?P {d}"
    using system_definition_closure_roots[of "{d}" ?P] by simp
  have rooted: "(d,decode_finite_term c) \<in> positive_meaning ?R"
    using holds root by (simp only: rooted_system_meaning[OF formed] simp_thms)
  have fixed: "\<forall>x\<in>system_leaves ?R. ?L x=x"
  proof
    fix x assume "x \<in> system_leaves ?R"
    then have "x \<in> system_leaves ?P"
      using system_leaves_restriction[of ?P "system_definition_closure ?P {d}"] unfolding rooted_system_def by blast
    then show "?L x=x" by (rule criticism_octet_leaf_map_fixes)
  qed
  have "(d,map_term_leaves ?L (decode_finite_term c)) \<in> positive_meaning ?R"
    by (rule positive_meaning_leaf_map[OF fixed criticism_octet_leaf_map_formed observation_free rooted])
  then have "(d,decode_finite_term (?s c)) \<in> positive_meaning ?R"
    by (simp only: decode_criticism_octet_sample)
  then have "(d,decode_finite_term c') \<in> positive_meaning ?P"
    using image by (simp only: rooted_system_meaning[OF formed])
  then show False using fails by simp
qed

corollary octet_sample_row_materials:
  assumes formed: "schema_system_formed (decode_finite_system P)"
    and table: "criticism_table P ds (octet_sample_pairs P ts)=Some A"
    and row: "(c,c',d,w) |\<in>| criticism_record ds (octet_sample_pairs P ts) A"
  shows "finite_entry_materials P d\<noteq>{||}"
    and "\<not>system_observation_free (rooted_system (decode_finite_system P) {d})"
proof -
  show materials: "finite_entry_materials P d\<noteq>{||}"
  proof
    assume free: "finite_entry_materials P d={||}"
    show False using octet_sample_no_row[OF formed free table] row by simp
  qed
  then show "\<not>system_observation_free (rooted_system (decode_finite_system P) {d})"
    using finite_entry_materials_exact[of P d] by simp
qed

definition octet_sample_rows ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      finite_factor_term list \<Rightarrow> ((finite_factor_term\<times>finite_factor_term\<times>local_address option definition_site)\<times>
        ((local_address option definition_site\<times>local_address)\<times>
          (local_address,local_address,local_address option definition_site) finite_factor_schema) fset) fset option" where
  "octet_sample_rows P ds ts=(case criticism_table P ds (octet_sample_pairs P ts) of None \<Rightarrow> None
    | Some A \<Rightarrow> Some (fimage (\<lambda>(c,c',d,w). ((c,c',d),finite_entry_materials P d))
        (criticism_record ds (octet_sample_pairs P ts) A)))"

theorem octet_sample_rows_materials:
  assumes formed: "schema_system_formed (decode_finite_system P)"
    and rows: "octet_sample_rows P ds ts=Some X" and member: "(r,M) |\<in>| X"
  shows "M\<noteq>{||}"
proof -
  obtain A where table: "criticism_table P ds (octet_sample_pairs P ts)=Some A"
    using rows by (auto simp: octet_sample_rows_def split: option.splits)
  obtain c c' d w where row: "(c,c',d,w) |\<in>| criticism_record ds (octet_sample_pairs P ts) A"
    and M: "M=finite_entry_materials P d"
    using rows member by (auto simp: octet_sample_rows_def table)
  show ?thesis using octet_sample_row_materials(1)[OF formed table row] M by simp
qed

section \<open>Controls\<close>

text \<open>
  One program with two entries. The first holds of a payload exactly when it is the address of the one
  atom of a stated target literal, observed by a material premise: the octet is read only through the
  target, not stated as a payload, so the sample moves it and records a row, listing the premise. The
  second, observation-free, holds of a pair of equal terms and records none.
\<close>

definition octet_control_target :: finite_exact_artifact where
  "octet_control_target=finite_enumerated_artifact [[5]] [] [] []"

definition octet_moved_target :: finite_exact_artifact where
  "octet_moved_target=finite_enumerated_artifact [[7]] [] [] []"

definition octet_control_end :: "local_address finite_term_pattern" where
  "octet_control_end=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)"

definition octet_control_material :: "local_address finite_material_pattern" where
  "octet_control_material=\<lparr>finite_material_source=Finite_Pattern_Target (Finite_Whole octet_control_target),
    finite_material_atoms=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Target (Finite_Anchor octet_control_target [5]))) octet_control_end,
    finite_material_edges=octet_control_end, finite_material_counts=octet_control_end,
    finite_material_functions=octet_control_end\<rparr>"

definition octet_material_entry :: "local_address option definition_site" where
  "octet_material_entry=(Some [4,3,6],[0])"

definition octet_equality_entry :: "local_address option definition_site" where
  "octet_equality_entry=(Some [4,3,6],[1])"

definition octet_control_program :: "local_address option finite_native_system" where
  "octet_control_program=finite_rule_program
    [(octet_material_entry,[([0],(finite_native_rule (native_var 0) [])
        \<lparr>finite_schema_materials:={|([1],octet_control_material)|}\<rparr>)]),
     (octet_equality_entry,[([0],finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 0)) [])])]"

definition octet_control_terms :: "finite_factor_term list" where
  "octet_control_terms=[Finite_Payload [5],Finite_Pair (Finite_Payload [5]) (Finite_Payload [5]),
    Finite_Pair (Finite_Payload [5]) (Finite_Payload [6]),
    Finite_Target (Finite_Whole octet_control_target),Finite_Target (Finite_Whole octet_moved_target)]"

definition octet_control_material_reading :: "unit \<Rightarrow> bool list" where
  "octet_control_material_reading _=(let P=octet_control_program; ts=octet_control_terms;
      ps=octet_sample_pairs P ts; p=Finite_Payload [5]; q=criticism_octet_sample P ts p in
    case criticism_table P [octet_material_entry] ps of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [finite_system_payloads P={||},q\<noteq>p,
        criticism_record [octet_material_entry] ps A={|(p,q,octet_material_entry,())|},
        criticism_refuted [octet_material_entry] ps A={|octet_material_entry|},
        finite_entry_materials P octet_material_entry\<noteq>{||},
        octet_sample_rows P [octet_material_entry] ts=
          Some {|((p,q,octet_material_entry),finite_entry_materials P octet_material_entry)|},
        criticism_octet_sample P ts (Finite_Target (Finite_Whole octet_control_target))=
          Finite_Target (Finite_Whole octet_control_target),
        criticism_octet_sample P ts (Finite_Target (Finite_Whole octet_moved_target))\<noteq>
          Finite_Target (Finite_Whole octet_moved_target)])"

definition octet_control_equality_reading :: "unit \<Rightarrow> bool list" where
  "octet_control_equality_reading _=(let P=octet_control_program; ts=octet_control_terms;
      ps=octet_sample_pairs P ts in
    case criticism_table P [octet_equality_entry] ps of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [finite_entry_materials P octet_equality_entry={||},
        criticism_record [octet_equality_entry] ps A={||},
        (octet_equality_entry,Finite_Pair (Finite_Payload [5]) (Finite_Payload [5])) |\<in>| A,
        (octet_equality_entry,criticism_octet_sample P ts (Finite_Pair (Finite_Payload [5]) (Finite_Payload [5]))) |\<in>| A])"

ML \<open>
  local
    fun run name f expected =
      let
        val (time, result) = Timing.timing f ()
        val shown = ML_Syntax.print_list Bool.toString result
      in
        if result = expected then writeln ("CRITICISM_OCTET_CONTROL " ^ name ^ " " ^ shown ^ " " ^ Timing.message time)
        else error ("Criticism octet control " ^ name ^ " differs: " ^ shown)
      end
  in
    val _ = run "material" @{code octet_control_material_reading} [true, true, true, true, true, true, true, true]
    val _ = run "equality" @{code octet_control_equality_reading} [true, true, true, true]
  end
\<close>

end
