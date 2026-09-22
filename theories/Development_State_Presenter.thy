theory Development_State_Presenter
imports Development_State_Rows Development_Entity_Keys
begin

section \<open>A rooted state presented as its rows\<close>

text \<open>
  \<open>state_presents\<close> is a relation: it carries every condition of a presentation and computes none. The
  presenter realizes it as a partial function, keyed once. A constant is keyed by the path of the binary
  digits of its position in the state's name table, the assignment a locus's key takes; an entity row by
  the first-occurrence key of its entity in the state's own entity list (\<open>development_entity_key\<close>), the
  key the contract question names its candidates by, so the state's rows, the requests' context
  citations and the question's candidates are one key assignment; a root row by the first-occurrence key
  of its root in the state's root list. A family holds each entity of its kind once, whatever
  repetitions the entity list has. The rows are presented as terms by \<open>state_row_term\<close> and
  \<open>state_family_term\<close> unchanged; the presenter adds no term presentation and no payload, and names stay
  the atoms' inert payloads.

  The presenter keys one state by its own first occurrences. An answer state keyed to share keys with its
  request state (\<open>keys_shared\<close>) is a presentation of a pair of states and is not stated here.
\<close>

definition state_constant_key :: "nat \<Rightarrow> state_key" where
  "state_constant_key=natural_binary_digits"

lemma state_constant_key_injective: "inj state_constant_key"
  by (rule injI) (simp add: state_constant_key_def)

subsection \<open>The three conditions a presentation carries, and their owners\<close>

text \<open>
  A state has a presentation exactly when three conditions hold, each of which \<open>state_presents\<close> carries
  and none of which the presenter repairs. Its names are distinct: for an answer state the answer's reader
  owns this, as it must refuse a duplicated name, and for an exported state the exporter. Every position a
  value of the state uses is a position of its table: the state's source owns this. Its roots are
  distinct as local presentations: the exporter that defines the state's roots owns this. A state outside
  them gets no rows, never rows that present it as another state.
\<close>

definition state_presentable :: "isabelle_rooted_context \<Rightarrow> bool" where
  "state_presentable S \<longleftrightarrow> distinct (fst (snd S)) \<and>
    state_positions S\<subseteq>{..<length (fst (snd S))} \<and>
    distinct (map (isabelle_local_root (fst (snd S))) (fst S))"

lemma state_positions_listed:
  "state_positions S=set (concat (map isabelle_entity_positions (snd (snd S))) @
    concat (map isabelle_term_positions (fst S)))"
  by (auto simp: state_positions_def)

lemma state_presentable_code [code]:
  "state_presentable S \<longleftrightarrow> distinct (fst (snd S)) \<and>
    list_all (\<lambda>i. i<length (fst (snd S))) (concat (map isabelle_entity_positions (snd (snd S))) @
      concat (map isabelle_term_positions (fst S))) \<and>
    distinct (map (isabelle_local_root (fst (snd S))) (fst S))"
  unfolding state_presentable_def state_positions_listed list_all_iff by auto

subsection \<open>The rows\<close>

definition state_rows_of :: "isabelle_rooted_context \<Rightarrow> state_rows" where
  "state_rows_of S=\<lparr>state_atoms=map (\<lambda>i. (state_constant_key i,fst (snd S)!i)) [0..<length (fst (snd S))],
    state_entities=(\<lambda>k. map (\<lambda>e. (development_entity_key (snd S) e,entity_row state_constant_key (snd S) e))
      (remdups (filter (\<lambda>e. entity_kind_of e=k) (snd (snd S))))),
    state_roots=map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (snd S) t)) (fst S)\<rparr>"

definition state_presenter :: "isabelle_rooted_context \<Rightarrow> state_rows option" where
  "state_presenter S=(if state_presentable S then Some (state_rows_of S) else None)"

lemma state_rows_of_presented:
  "presented_rows (state_rows_of S)=
    (\<lambda>e. (development_entity_key (snd S) e,entity_row state_constant_key (snd S) e)) ` set (snd (snd S))"
  by (auto simp: presented_rows_def state_rows_of_def)

subsection \<open>One state's embedding into itself fixes its values\<close>

lemma state_self_embedding:
  assumes distinct: "distinct names" and bound: "i<length names"
  shows "isabelle_state_embedding names names i=i"
proof -
  have "isabelle_table_correspondence id names names"
    by (simp add: isabelle_table_correspondence_def)
  then show ?thesis using isabelle_state_embedding_agrees[OF distinct _ bound] by simp
qed

lemma state_self_embedding_entity:
  assumes distinct: "distinct names" and inside: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
  shows "isabelle_entity_rename (isabelle_state_embedding names names) e=e"
proof -
  have "isabelle_entity_rename (isabelle_state_embedding names names) e=isabelle_entity_rename id e"
    by (rule isabelle_entity_rename_cong) (simp add: state_self_embedding[OF distinct] inside)
  then show ?thesis by (simp only: isabelle_entity_rename_id)
qed

text \<open>
  Within one state, two entities have one local presentation exactly when they are one entity: the
  comparison of local presentations across two states (\<open>isabelle_local_entities_compared\<close>) at equal tables.
  It is stated once for any table free of repeated names that holds the positions both entities use, and a
  presentable state is its instance.
\<close>

lemma local_entities_injective_within:
  assumes distinct: "distinct names"
    and ie: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
    and ig: "\<forall>i\<in>set (isabelle_entity_positions g). i<length names"
  shows "isabelle_local_entities names [e]=isabelle_local_entities names [g] \<longleftrightarrow> e=g"
proof -
  have "isabelle_local_entities names [e]=isabelle_local_entities names [g] \<longleftrightarrow>
      isabelle_entity_rename (isabelle_state_embedding names names) e=g"
    by (rule isabelle_local_entities_compared[OF distinct ie ig])
  then show ?thesis using state_self_embedding_entity[OF distinct ie] by simp
qed

lemma state_local_entities_injective:
  assumes presentable: "state_presentable S"
    and e: "e\<in>set (snd (snd S))" and g: "g\<in>set (snd (snd S))"
    and same: "isabelle_local_entities (fst (snd S)) [e]=isabelle_local_entities (fst (snd S)) [g]"
  shows "e=g"
proof -
  have distinct: "distinct (fst (snd S))" and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}"
    using presentable by (simp_all add: state_presentable_def)
  have ie: "\<forall>i\<in>set (isabelle_entity_positions e). i<length (fst (snd S))"
    using inside e by (auto simp: state_positions_def)
  have ig: "\<forall>j\<in>set (isabelle_entity_positions g). j<length (fst (snd S))"
    using inside g by (auto simp: state_positions_def)
  show ?thesis using local_entities_injective_within[OF distinct ie ig] same by simp
qed

subsection \<open>Rows keyed injectively present a presentable state\<close>

text \<open>
  A presentable state is presented by any rows whose atoms are its positions keyed by the constant key, whose
  families hold exactly its entities of their kind at keys an injective entity key assigns, each family keyed
  once, and whose roots are its roots at keys an injective root key assigns. The presenter is the instance at
  the first-occurrence keys; an edited state is the instance at keys continuing its request state's.
\<close>

lemma state_presents_keyed:
  assumes presentable: "state_presentable S"
    and atoms: "state_atoms R=map (\<lambda>i. (state_constant_key i,fst (snd S)!i)) [0..<length (fst (snd S))]"
    and families: "\<And>k. set (state_entities R k)=
      (\<lambda>e. (\<kappa> e,entity_row state_constant_key (snd S) e)) ` {e\<in>set (snd (snd S)). entity_kind_of e=k}"
    and keyed: "\<And>k. distinct (map fst (state_entities R k))"
    and injective: "inj_on \<kappa> (set (snd (snd S)))"
    and roots: "state_roots R=map (\<lambda>t. (\<rho> t,root_row state_constant_key (snd S) t)) (fst S)"
    and root_keys: "inj_on \<rho> (set (fst S))"
  shows "state_presents state_constant_key S R"
proof -
  have distinct: "distinct (fst (snd S))" and inside: "state_positions S\<subseteq>{..<length (fst (snd S))}"
    and local_roots: "distinct (map (isabelle_local_root (fst (snd S))) (fst S))"
    using presentable by (simp_all add: state_presentable_def)
  have atoms_ok: "atoms_present state_constant_key (fst (snd S)) R"
  proof -
    have fsts: "map fst (state_atoms R)=map state_constant_key [0..<length (fst (snd S))]"
      by (simp only: atoms map_map comp_def fst_conv)
    have snds: "map snd (state_atoms R)=fst (snd S)"
      by (simp only: atoms map_map comp_def snd_conv map_nth)
    have set_atoms: "set (state_atoms R)=(\<lambda>i. (state_constant_key i,fst (snd S)!i)) ` {..<length (fst (snd S))}"
      by (simp only: atoms set_map set_upt atLeast0LessThan)
    have length_atoms: "length (state_atoms R)=length (fst (snd S))"
      by (simp only: atoms length_map length_upt diff_zero)
    have "distinct (map state_constant_key [0..<length (fst (snd S))])"
      using inj_on_subset[OF state_constant_key_injective] by (simp add: distinct_map)
    then show ?thesis using distinct fsts snds set_atoms length_atoms
      by (simp only: atoms_present_def)
  qed
  have rows_ok: "rows_present state_constant_key (snd S) R"
  proof -
    have "set (map snd (state_entities R k))=
        entity_row state_constant_key (snd S) ` {e\<in>set (snd (snd S)). entity_kind_of e=k}" for k
      by (simp add: families image_image)
    then show ?thesis using keyed by (simp add: rows_present_def)
  qed
  have roots_ok: "roots_present state_constant_key (snd S) (fst S) R"
  proof -
    have "distinct (fst S)" using local_roots by (simp add: distinct_map)
    then have "distinct (map \<rho> (fst S))" using root_keys by (simp add: distinct_map)
    then show ?thesis by (simp add: roots_present_def roots comp_def)
  qed
  have presented: "presented_rows R=(\<lambda>e. (\<kappa> e,entity_row state_constant_key (snd S) e)) ` set (snd (snd S))"
    unfolding presented_rows_def families by blast
  have row_keys: "keyed_agree row_identity (presented_rows R) (presented_rows R)"
  proof (rule keyed_agreeI)
    fix a x b y assume "(a,x)\<in>presented_rows R" "(b,y)\<in>presented_rows R"
    then obtain e g where e: "e\<in>set (snd (snd S))" "a=\<kappa> e" "x=entity_row state_constant_key (snd S) e"
      and g: "g\<in>set (snd (snd S))" "b=\<kappa> g" "y=entity_row state_constant_key (snd S) g"
      unfolding presented by auto
    have "(a=b)=(e=g)" using e(2) g(2) inj_onD[OF injective _ e(1) g(1)] by auto
    moreover have "(e=g)=(row_identity x=row_identity y)"
      using e g state_local_entities_injective[OF presentable] by auto
    ultimately show "(a=b)=(row_identity x=row_identity y)" by simp
  qed
  have root_keys_ok: "keyed_agree row_identity (set (state_roots R)) (set (state_roots R))"
  proof (rule keyed_agreeI)
    fix a x b y assume "(a,x)\<in>set (state_roots R)" "(b,y)\<in>set (state_roots R)"
    then obtain t u where t: "t\<in>set (fst S)" "a=\<rho> t" "x=root_row state_constant_key (snd S) t"
      and u: "u\<in>set (fst S)" "b=\<rho> u" "y=root_row state_constant_key (snd S) u"
      by (auto simp: roots)
    have local: "inj_on (isabelle_local_root (fst (snd S))) (set (fst S))"
      using local_roots by (simp add: distinct_map)
    have "(a=b)=(t=u)" using t(2) u(2) inj_onD[OF root_keys _ t(1) u(1)] by auto
    moreover have "(t=u)=(row_identity x=row_identity y)"
      using t u inj_onD[OF local] by auto
    ultimately show "(a=b)=(row_identity x=row_identity y)" by simp
  qed
  show ?thesis
    using atoms_ok rows_ok roots_ok inside row_keys root_keys_ok by (simp add: state_presents_def)
qed

subsection \<open>The presenter realizes the relation\<close>

theorem state_presenter_presents:
  assumes presented: "state_presenter S=Some R"
  shows "state_presents state_constant_key S R"
proof -
  have presentable: "state_presentable S" and R: "R=state_rows_of S"
    using presented by (simp_all add: state_presenter_def split: if_splits)
  have atoms: "state_atoms R=map (\<lambda>i. (state_constant_key i,fst (snd S)!i)) [0..<length (fst (snd S))]"
    by (simp add: R state_rows_of_def)
  have families: "\<And>k. set (state_entities R k)=(\<lambda>e. (development_entity_key (snd S) e,
      entity_row state_constant_key (snd S) e)) ` {e\<in>set (snd (snd S)). entity_kind_of e=k}"
    by (auto simp: R state_rows_of_def)
  have keyed: "\<And>k. distinct (map fst (state_entities R k))"
  proof -
    fix k
    have "distinct (map (development_entity_key (snd S)) (remdups (filter (\<lambda>e. entity_kind_of e=k) (snd (snd S)))))"
      using inj_on_subset[OF development_entity_key_injective] by (auto simp: distinct_map)
    then show "distinct (map fst (state_entities R k))" by (simp add: R state_rows_of_def comp_def)
  qed
  have roots: "state_roots R=map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (snd S) t)) (fst S)"
    by (simp add: R state_rows_of_def)
  show ?thesis
    by (rule state_presents_keyed[OF presentable atoms families keyed development_entity_key_injective roots
      first_occurrence_key_inj_on])
qed

subsection \<open>The partiality is exact\<close>

theorem state_presenter_defined:
  "state_presenter S\<noteq>None \<longleftrightarrow> state_presentable S"
  by (simp add: state_presenter_def)

text \<open>
  A state that has a presentation at all, under any key, meets the three conditions: they are the
  consequences \<open>state_presents_distinct_names\<close>, \<open>state_presents_inside\<close> and
  \<open>state_presents_distinct_roots\<close> derive. So the presenter returns rows exactly when the state has a
  presentation, and refuses exactly the states that have none.
\<close>

theorem state_presents_presentable:
  assumes "state_presents key S R"
  shows "state_presentable S"
  using state_presents_distinct_names[OF assms] state_presents_inside[OF assms]
    state_presents_distinct_roots[OF assms]
  by (simp add: state_presentable_def)

theorem state_presenter_exact:
  "state_presenter S\<noteq>None \<longleftrightarrow> (\<exists>R. state_presents state_constant_key S R)"
  using state_presenter_presents state_presents_presentable state_presenter_defined by blast

theorem state_presenter_exact_any_key:
  "state_presenter S\<noteq>None \<longleftrightarrow> (\<exists>key R. state_presents key S R)"
  using state_presenter_presents state_presents_presentable state_presenter_defined by blast

subsection \<open>Every entity stands at its first-occurrence key\<close>

text \<open>
  The entity-key condition: every entity of the state has its row in the family of its kind at its
  first-occurrence key, the key the contract question names it by and the requests' context cites it by.
\<close>

theorem state_presenter_entity_key:
  assumes presented: "state_presenter S=Some R" and member: "e\<in>set (snd (snd S))"
  shows "(development_entity_key (snd S) e,entity_row state_constant_key (snd S) e)
      \<in>set (state_entities R (entity_kind_of e))"
    "(development_entity_key (snd S) e,entity_row state_constant_key (snd S) e)\<in>presented_rows R"
proof -
  have R: "R=state_rows_of S" using presented by (simp add: state_presenter_def split: if_splits)
  show first: "(development_entity_key (snd S) e,entity_row state_constant_key (snd S) e)
      \<in>set (state_entities R (entity_kind_of e))"
    using member by (simp add: R state_rows_of_def)
  then show "(development_entity_key (snd S) e,entity_row state_constant_key (snd S) e)\<in>presented_rows R"
    by (rule presented_rows_member)
qed

theorem state_presenter_root_key:
  assumes presented: "state_presenter S=Some R" and member: "t\<in>set (fst S)"
  shows "(first_occurrence_key (fst S) t,root_row state_constant_key (snd S) t)\<in>set (state_roots R)"
  using presented member by (auto simp: state_presenter_def state_rows_of_def split: if_splits)

text \<open>
  The rows' entity key is the one \<open>request_presents\<close> fixes for a state and the key the contract question
  names candidates by; the constant key is the one it takes for the state's and the development's rows.
\<close>

end
