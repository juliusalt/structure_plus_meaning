theory Development_State_Edit
  imports Development_State_Presenter Development_Verdict_Difference Development_Native_Answers
    Member_Tree_Indexes Ordered_Finite_Terms
begin

section \<open>An answer is an edit of its request state's rows\<close>

text \<open>
  An answer's edit is three families: the atoms \<open>N\<close> it appends, the rows \<open>D\<close> it removes and the rows
  \<open>A\<close> it adds, \<open>D\<close> and \<open>A\<close> each by kind, since a kind is the family that holds a row. The answer
  state's presentation is the request state's updated by the edit: the atoms followed by \<open>N\<close>, each family
  without \<open>D\<close>'s rows followed by \<open>A\<close>'s, the roots unchanged. Nothing is read from the answer state that the
  edit does not state, and the edit's term holds its names and rows only.
\<close>

record state_edit =
  edit_atoms :: "(state_key\<times>String.literal) list"
  edit_removed :: "entity_kind \<Rightarrow> isabelle_context state_family"
  edit_added :: "entity_kind \<Rightarrow> isabelle_context state_family"

definition edit_rows :: "(entity_kind \<Rightarrow> 'i state_family) \<Rightarrow> (state_key\<times>'i state_row) set" where
  "edit_rows F=(\<Union>k. set (F k))"

definition edited_state :: "state_rows \<Rightarrow> state_edit \<Rightarrow> state_rows" where
  "edited_state R e=\<lparr>state_atoms=state_atoms R@edit_atoms e,
    state_entities=(\<lambda>k. filter (\<lambda>z. z\<notin>set (edit_removed e k)) (state_entities R k)@edit_added e k),
    state_roots=state_roots R\<rparr>"

subsection \<open>The answer state an edit makes\<close>

text \<open>
  The answer state is read into the request state's table extended by the names it lacks
  (\<open>isabelle_appended_names\<close>), so every constant keeps its position; its entities are the request state's
  without the removed ones, in the request state's order, followed by the added ones; its roots are the
  request state's. The removed and added entities are stated in the extended table.
\<close>

definition edit_applied :: "isabelle_rooted_context \<Rightarrow> String.literal list \<Rightarrow> isabelle_entity list \<Rightarrow>
    isabelle_entity list \<Rightarrow> isabelle_rooted_context" where
  "edit_applied S ns removed added=(fst S,(isabelle_appended_names (fst (snd S)) ns,
    filter (\<lambda>e. e\<notin>set removed) (snd (snd S))@added))"

subsection \<open>The specification condition\<close>

text \<open>
  A specification's subjects are the development constants it mentions, read against the whole development
  family. An edit that adds or removes the development declaration of a constant a specification of the
  request state mentions changes that specification's row at its kept key, which a reduced edit has no place
  for. The condition is that no specification of the request state mentions such a constant.
\<close>

definition edit_specification_condition :: "isabelle_entity list \<Rightarrow> isabelle_entity list \<Rightarrow> bool" where
  "edit_specification_condition E E' \<longleftrightarrow> list_all (\<lambda>e. case e of
     Isabelle_Specification p \<Rightarrow> list_all (\<lambda>c. (c\<in>set (isabelle_development_constants E))=
       (c\<in>set (isabelle_development_constants E'))) (isabelle_term_constants p)
   | _ \<Rightarrow> True) E"

lemma edit_specification_condition_at:
  assumes condition: "edit_specification_condition E E'"
    and member: "Isabelle_Specification p\<in>set E" and mentioned: "c\<in>set (isabelle_term_constants p)"
  shows "(c\<in>set (isabelle_development_constants E))=(c\<in>set (isabelle_development_constants E'))"
proof -
  have "case Isabelle_Specification p of Isabelle_Specification p \<Rightarrow> list_all (\<lambda>c. (c\<in>set (isabelle_development_constants E))=
       (c\<in>set (isabelle_development_constants E'))) (isabelle_term_constants p) | _ \<Rightarrow> True"
    using condition member unfolding edit_specification_condition_def list_all_iff by (rule bspec)
  then show ?thesis using mentioned by (simp add: list_all_iff)
qed

subsection \<open>The constructor\<close>

text \<open>
  The edit's rows are the rows of the true difference: a removed entity that is added again, or an added
  entity the request state already holds, stays at its row. A removed row is the request state's row at its
  key there; an added row's key is the first-occurrence key of its entity in the request state's entity list
  followed by the added entities, which continues the request state's keys and is never the key of one of its
  rows, so a removed row's key is retired and never reused. The constructor refuses exactly an edit that fails
  the specification condition; its refusal is no verdict: the answer state is then judged whole.
\<close>

definition state_edit_of :: "isabelle_rooted_context \<Rightarrow> String.literal list \<Rightarrow> isabelle_entity list \<Rightarrow>
    isabelle_entity list \<Rightarrow> state_edit option" where
  "state_edit_of S ns removed added=(let E=snd (snd S); S'=edit_applied S ns removed added;
     names=fst (snd S); names'=fst (snd S');
     gone=remdups (filter (\<lambda>d. d\<in>set removed \<and> d\<notin>set added) E);
     new=remdups (filter (\<lambda>a. a\<notin>set E) added) in
     if edit_specification_condition E (snd (snd S')) then
       Some \<lparr>edit_atoms=map (\<lambda>i. (state_constant_key i,names'!i)) [length names..<length names'],
         edit_removed=(\<lambda>k. map (\<lambda>d. (development_entity_key (snd S) d,entity_row state_constant_key (snd S) d))
           (filter (\<lambda>d. entity_kind_of d=k) gone)),
         edit_added=(\<lambda>k. map (\<lambda>a. (first_occurrence_key (E@added) a,entity_row state_constant_key (snd S') a))
           (filter (\<lambda>a. entity_kind_of a=k) new))\<rparr>
     else None)"

theorem state_edit_of_refuses:
  "state_edit_of S ns removed added=None \<longleftrightarrow>
    \<not>edit_specification_condition (snd (snd S)) (snd (snd (edit_applied S ns removed added)))"
  by (simp add: state_edit_of_def Let_def)

section \<open>What the contract rests on\<close>

text \<open>
  Keys continue because a first occurrence in a prefix stays where it was (\<open>first_occurrence_key_append\<close>),
  and a value's reading depends on the names at the positions it uses (the notion \<open>isabelle_name_reading\<close>,
  whose instances are the local presentations of entities and roots and the subjects of an entity); both are
  stated with their notions.
\<close>

text \<open>
  A kept entity has the same row in the answer state as in the request state: its names are at the same
  positions of the extended table, and, under the specification condition, a specification reads the same
  development constants.
\<close>

lemma entity_row_kept:
  assumes prefix: "\<And>i. i<length names \<Longrightarrow> isabelle_name_at names' i=isabelle_name_at names i"
    and inside: "\<forall>i\<in>set (isabelle_entity_positions e). i<length names"
    and specified: "\<And>p c. e=Isabelle_Specification p \<Longrightarrow> c\<in>set (isabelle_term_constants p) \<Longrightarrow>
      (c\<in>set (isabelle_development_constants E'))=(c\<in>set (isabelle_development_constants E))"
  shows "entity_row key (names',E') e=entity_row key (names,E) e"
proof -
  have agree: "isabelle_name_at names' i=isabelle_name_at names i"
    if "i\<in>set (isabelle_entity_positions e)" for i
    using prefix inside that by blast
  have subjects: "isabelle_entity_subjects names' (isabelle_development_constants E') e=
      isabelle_entity_subjects names (isabelle_development_constants E) e"
  proof -
    have "isabelle_entity_subjects names' (isabelle_development_constants E') e=
        isabelle_entity_subjects names (isabelle_development_constants E') e"
      by (rule isabelle_name_reading.agree[OF isabelle_entity_subjects_reading]) (rule agree)
    also have "\<dots>=isabelle_entity_subjects names (isabelle_development_constants E) e"
    proof (cases e)
      case (Isabelle_Specification p)
      have "filter (\<lambda>c. c\<in>set (isabelle_development_constants E')) (isabelle_term_constants p)=
          filter (\<lambda>c. c\<in>set (isabelle_development_constants E)) (isabelle_term_constants p)"
        by (rule filter_cong[OF refl]) (rule specified[OF Isabelle_Specification])
      then show ?thesis by (simp add: Isabelle_Specification)
    qed simp_all
    finally show ?thesis .
  qed
  have identity: "isabelle_local_entities names' [e]=isabelle_local_entities names [e]"
    by (rule isabelle_name_reading.agree[OF isabelle_local_entities_reading]) (rule agree, simp)
  show ?thesis by (simp add: entity_row_def subjects identity)
qed

section \<open>The constructor's contract\<close>

text \<open>
  For a request state presented by its presenter and an answer state that is an edit applied to it, the
  edited presentation presents the answer state, shares its keys with the request state's, is reduced by the
  edit, and keeps the roots. Keys continue: every constant keeps its key and the appended atoms' keys are
  new; every kept entity keeps its row at its key; a removed row's key is no key of the answer state; an added
  row's key is no key of the request state. These are the constructor's contract, stated once with it; no
  field of the verdict checks them again.
\<close>

theorem state_edit_contract:
  fixes S :: isabelle_rooted_context and ns :: "String.literal list" and removed added :: "isabelle_entity list"
  defines "S'\<equiv>edit_applied S ns removed added"
  assumes presented: "state_presenter S=Some R"
    and answer: "state_presentable S'"
    and edit: "state_edit_of S ns removed added=Some e"
  shows "state_presents state_constant_key S' (edited_state R e)"
    and "keys_shared R (edited_state R e)"
    and "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and "state_roots (edited_state R e)=state_roots R"
    and "\<And>z. z\<in>presented_rows R \<Longrightarrow> z\<notin>edit_rows (edit_removed e) \<Longrightarrow> z\<in>presented_rows (edited_state R e)"
    and "\<And>a n. (a,n)\<in>set (edit_atoms e) \<Longrightarrow> a\<notin>fst ` set (state_atoms R)"
    and "\<And>g. g\<in>set (snd (snd S)) \<Longrightarrow> g\<in>set (snd (snd S')) \<Longrightarrow>
      (development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
        \<in>set (state_entities (edited_state R e) (entity_kind_of g))"
    and "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and "\<And>b q. (b,q)\<in>edit_rows (edit_added e) \<Longrightarrow> b\<notin>fst ` presented_rows R"
proof -
  let ?names="fst (snd S)" and ?E="snd (snd S)"
  let ?names'="isabelle_appended_names ?names ns"
  let ?E'="filter (\<lambda>e. e\<notin>set removed) ?E@added"
  let ?gone="remdups (filter (\<lambda>d. d\<in>set removed \<and> d\<notin>set added) ?E)"
  let ?new="remdups (filter (\<lambda>a. a\<notin>set ?E) added)"
  let ?\<kappa>="first_occurrence_key (?E@added)"
  let ?row="entity_row state_constant_key (snd S)"
  let ?row'="entity_row state_constant_key (?names',?E')"
  let ?f="\<lambda>g. (?\<kappa> g,?row' g)"
  have S': "S'=(fst S,(?names',?E'))" by (simp add: S'_def edit_applied_def)
  have R: "R=state_rows_of S" and presentable: "state_presentable S"
    using presented by (simp_all add: state_presenter_def split: if_splits)
  have present: "state_presents state_constant_key S R" by (rule state_presenter_presents[OF presented])
  have inside: "state_positions S\<subseteq>{..<length ?names}"
    using presentable by (simp add: state_presentable_def)
  have distinct': "distinct ?names'" and inside': "state_positions S'\<subseteq>{..<length ?names'}"
    using answer by (simp_all add: state_presentable_def S')
  have condition: "edit_specification_condition ?E ?E'"
    using edit by (simp add: state_edit_of_def edit_applied_def Let_def split: if_splits)
  have e: "e=\<lparr>edit_atoms=map (\<lambda>i. (state_constant_key i,?names'!i)) [length ?names..<length ?names'],
      edit_removed=(\<lambda>k. map (\<lambda>d. (development_entity_key (snd S) d,?row d)) (filter (\<lambda>d. entity_kind_of d=k) ?gone)),
      edit_added=(\<lambda>k. map ?f (filter (\<lambda>a. entity_kind_of a=k) ?new))\<rparr>"
    using edit by (simp add: state_edit_of_def edit_applied_def Let_def split: if_splits)
  have longer: "length ?names\<le>length ?names'" by (rule isabelle_appended_names_longer)
  have prefix: "isabelle_name_at ?names' i=isabelle_name_at ?names i" if "i<length ?names" for i
    using that by (rule isabelle_appended_names_prefix)
  have nth_prefix: "?names'!i=?names!i" if "i<length ?names" for i
    using that by (rule isabelle_appended_names_nth)
  have old_inside: "\<forall>i\<in>set (isabelle_entity_positions g). i<length ?names" if "g\<in>set ?E" for g
    using that inside by (auto simp: state_positions_def)
  have new_inside: "\<forall>i\<in>set (isabelle_entity_positions g). i<length ?names'" if "g\<in>set ?E'" for g
    using that inside' by (auto simp: S' state_positions_def)
  have spec: "(c\<in>set (isabelle_development_constants ?E'))=(c\<in>set (isabelle_development_constants ?E))"
    if "Isabelle_Specification p\<in>set ?E" "c\<in>set (isabelle_term_constants p)" for p c
    using edit_specification_condition_at[OF condition that] by simp
  have kept: "?row' g=?row g" if g: "g\<in>set ?E" for g
  proof -
    have "entity_row state_constant_key (?names',?E') g=entity_row state_constant_key (?names,?E) g"
      by (rule entity_row_kept[OF prefix old_inside[OF g]]) (use spec g in auto)
    then show ?thesis by simp
  qed
  have \<kappa>_inj: "inj_on ?\<kappa> (set (?E@added))" by (rule first_occurrence_key_inj_on)
  have \<kappa>_old: "development_entity_key (snd S) g=?\<kappa> g" if "g\<in>set ?E" for g
    using first_occurrence_key_append[OF that, of added] by (simp add: development_entity_key_def)
  have f_old: "(development_entity_key (snd S) g,?row g)=?f g" if "g\<in>set ?E" for g
    using \<kappa>_old[OF that] kept[OF that] by simp
  have f_inj: "inj_on ?f (set (?E@added))"
    using \<kappa>_inj unfolding inj_on_def by blast
  have R_families: "set (state_entities R k)=?f ` {g\<in>set ?E. entity_kind_of g=k}" for k
  proof -
    have "set (state_entities R k)=(\<lambda>g. (development_entity_key (snd S) g,?row g)) ` {g\<in>set ?E. entity_kind_of g=k}"
      by (auto simp: R state_rows_of_def)
    also have "\<dots>=?f ` {g\<in>set ?E. entity_kind_of g=k}"
      by (rule image_cong[OF refl]) (rule f_old, simp)
    finally show ?thesis .
  qed
  have R_rows: "presented_rows R=?f ` set ?E"
    unfolding presented_rows_def R_families by blast
  have Dk: "set (edit_removed e k)=?f ` {d\<in>set ?gone. entity_kind_of d=k}" for k
  proof -
    have "set (edit_removed e k)=(\<lambda>d. (development_entity_key (snd S) d,?row d)) ` {d\<in>set ?gone. entity_kind_of d=k}"
      by (auto simp: e)
    also have "\<dots>=?f ` {d\<in>set ?gone. entity_kind_of d=k}"
      by (rule image_cong[OF refl]) (rule f_old, auto)
    finally show ?thesis .
  qed
  have Ak: "set (edit_added e k)=?f ` {a\<in>set ?new. entity_kind_of a=k}" for k
    by (auto simp: e)
  have D_rows: "edit_rows (edit_removed e)=?f ` set ?gone"
    unfolding edit_rows_def Dk by blast
  have A_rows: "edit_rows (edit_added e)=?f ` set ?new"
    unfolding edit_rows_def Ak by blast
  have index: "(set ?E-set ?gone)\<union>set ?new=set ?E'" by auto
  have families': "set (state_entities (edited_state R e) k)=?f ` {g\<in>set ?E'. entity_kind_of g=k}" for k
  proof -
    have "set (state_entities (edited_state R e) k)=(set (state_entities R k)-set (edit_removed e k))\<union>set (edit_added e k)"
      by (auto simp: edited_state_def)
    also have "\<dots>=(?f ` {g\<in>set ?E. entity_kind_of g=k}-?f ` {d\<in>set ?gone. entity_kind_of d=k})\<union>
        ?f ` {a\<in>set ?new. entity_kind_of a=k}"
      by (simp only: R_families Dk Ak)
    also have "\<dots>=?f ` (({g\<in>set ?E. entity_kind_of g=k}-{d\<in>set ?gone. entity_kind_of d=k})\<union>
        {a\<in>set ?new. entity_kind_of a=k})"
      by (subst image_Un, subst inj_on_image_set_diff[OF f_inj]) auto
    also have "({g\<in>set ?E. entity_kind_of g=k}-{d\<in>set ?gone. entity_kind_of d=k})\<union>
        {a\<in>set ?new. entity_kind_of a=k}={g\<in>set ?E'. entity_kind_of g=k}"
      using index by blast
    finally show ?thesis .
  qed
  have R'_rows: "presented_rows (edited_state R e)=?f ` set ?E'"
    unfolding presented_rows_def families' by blast
  have keyed': "distinct (map fst (state_entities (edited_state R e) k))" for k
  proof -
    have old: "distinct (map fst (state_entities R k))"
      using state_presents_rows[OF present] by (simp add: rows_present_def)
    have new: "distinct (map fst (edit_added e k))"
    proof -
      have "map fst (edit_added e k)=map ?\<kappa> (filter (\<lambda>a. entity_kind_of a=k) ?new)" by (simp add: e)
      moreover have "inj_on ?\<kappa> (set (filter (\<lambda>a. entity_kind_of a=k) ?new))"
        by (rule inj_on_subset[OF \<kappa>_inj]) auto
      ultimately show ?thesis by (simp add: distinct_map)
    qed
    have apart: "set (map fst (filter (\<lambda>z. z\<notin>set (edit_removed e k)) (state_entities R k)))\<inter>
        set (map fst (edit_added e k))={}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain z w where z: "z\<in>set (state_entities R k)" and w: "w\<in>set (edit_added e k)"
        and same: "fst z=fst w" by auto
      obtain g where g: "g\<in>set ?E" "z=?f g" using z R_families by auto
      obtain a where a: "a\<in>set ?new" "w=?f a" using w Ak by auto
      have "?\<kappa> g=?\<kappa> a" using same g(2) a(2) by simp
      then have "g=a" by (rule inj_onD[OF \<kappa>_inj]) (use g a in auto)
      then show False using g a by simp
    qed
    show ?thesis using old new apart by (simp add: edited_state_def distinct_map_filter)
  qed
  have roots_same: "root_row state_constant_key (?names',?E') t=root_row state_constant_key (snd S) t"
    if t: "t\<in>set (fst S)" for t
  proof -
    have "isabelle_local_root ?names' t=isabelle_local_root ?names t"
    proof (rule isabelle_local_root_appended)
      fix i assume "i\<in>set (isabelle_term_positions t)"
      then show "i<length ?names" using t inside by (auto simp: state_positions_def)
    qed
    then show ?thesis by (simp add: root_row_def)
  qed
  have roots': "state_roots (edited_state R e)=
      map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (?names',?E') t)) (fst S)"
  proof -
    have "state_roots (edited_state R e)=
        map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (snd S) t)) (fst S)"
      by (simp add: edited_state_def R state_rows_of_def)
    also have "\<dots>=map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (?names',?E') t)) (fst S)"
      by (rule map_cong[OF refl]) (simp add: roots_same)
    finally show ?thesis .
  qed
  have atoms': "state_atoms (edited_state R e)=map (\<lambda>i. (state_constant_key i,?names'!i)) [0..<length ?names']"
  proof -
    obtain m where m: "length ?names'=length ?names+m" using longer le_iff_add by blast
    have upto: "[0..<length ?names']=[0..<length ?names]@[length ?names..<length ?names']"
      using upt_add_eq_append[of 0 "length ?names" m] m by simp
    have same: "map (\<lambda>i. (state_constant_key i,?names!i)) [0..<length ?names]=
        map (\<lambda>i. (state_constant_key i,?names'!i)) [0..<length ?names]"
      by (rule map_cong[OF refl]) (simp add: nth_prefix)
    show ?thesis by (simp add: edited_state_def R state_rows_of_def e upto same)
  qed
  show present': "state_presents state_constant_key S' (edited_state R e)"
  proof (rule state_presents_keyed[where \<kappa>="?\<kappa>" and \<rho>="first_occurrence_key (fst S)"])
    show "state_presentable S'" by (rule answer)
    show "state_atoms (edited_state R e)=map (\<lambda>i. (state_constant_key i,fst (snd S')!i)) [0..<length (fst (snd S'))]"
      unfolding S' prod.sel by (rule atoms')
    show "set (state_entities (edited_state R e) k)=
        (\<lambda>g. (?\<kappa> g,entity_row state_constant_key (snd S') g)) ` {g\<in>set (snd (snd S')). entity_kind_of g=k}" for k
      unfolding S' prod.sel by (rule families')
    show "distinct (map fst (state_entities (edited_state R e) k))" for k by (rule keyed')
    show "inj_on ?\<kappa> (set (snd (snd S')))"
      unfolding S' prod.sel by (rule inj_on_subset[OF \<kappa>_inj]) auto
    show "state_roots (edited_state R e)=map (\<lambda>t. (first_occurrence_key (fst S) t,root_row state_constant_key (snd S') t)) (fst S')"
      unfolding S' prod.sel by (rule roots')
    show "inj_on (first_occurrence_key (fst S)) (set (fst S'))"
      unfolding S' prod.sel by (rule first_occurrence_key_inj_on)
  qed
  have atoms_shared: "keyed_agree id (set (state_atoms R)) (set (state_atoms (edited_state R e)))"
  proof (rule keyed_agreeI)
    fix a x b y assume ax: "(a,x)\<in>set (state_atoms R)" and "(b,y)\<in>set (state_atoms (edited_state R e))"
    then obtain j where j: "j<length ?names'" "b=state_constant_key j" "y=?names'!j"
      unfolding atoms' by auto
    obtain i where i: "i<length ?names" "a=state_constant_key i" "x=?names!i"
      using ax by (auto simp: R state_rows_of_def)
    have "(a=b)=(i=j)" using i(2) j(2) state_constant_key_injective by (auto dest: injD)
    moreover have "(x=y)=(i=j)"
    proof -
      have x: "x=?names'!i" using i nth_prefix by simp
      have "i<length ?names'" using i(1) longer by simp
      then show ?thesis using x j(1) j(3) distinct' by (simp add: nth_eq_iff_index_eq)
    qed
    ultimately show "(a=b)=(id x=id y)" by simp
  qed
  have rows_shared: "keyed_agree row_identity (presented_rows R) (presented_rows (edited_state R e))"
  proof (rule keyed_agreeI)
    fix a x b y assume "(a,x)\<in>presented_rows R" "(b,y)\<in>presented_rows (edited_state R e)"
    then obtain g h where g: "g\<in>set ?E" "a=?\<kappa> g" "x=?row' g" and h: "h\<in>set ?E'" "b=?\<kappa> h" "y=?row' h"
      unfolding R_rows R'_rows by auto
    have gi: "\<forall>i\<in>set (isabelle_entity_positions g). i<length ?names'" using old_inside[OF g(1)] longer by auto
    have hi: "\<forall>i\<in>set (isabelle_entity_positions h). i<length ?names'" by (rule new_inside[OF h(1)])
    have "(a=b)=(g=h)"
    proof
      assume "a=b"
      then have "?\<kappa> g=?\<kappa> h" using g(2) h(2) by simp
      then show "g=h" by (rule inj_onD[OF \<kappa>_inj]) (use g(1) h(1) in auto)
    qed (use g h in simp)
    moreover have "(row_identity x=row_identity y)=(g=h)"
      using local_entities_injective_within[OF distinct' gi hi] g(3) h(3) by simp
    ultimately show "(a=b)=(row_identity x=row_identity y)" by simp
  qed
  have roots_shared: "keyed_agree row_identity (set (state_roots R)) (set (state_roots (edited_state R e)))"
    using state_presents_root_keys[OF present] by (simp add: edited_state_def)
  show "keys_shared R (edited_state R e)"
    using atoms_shared rows_shared roots_shared by (simp add: keys_shared_def)
  have fresh: "b\<notin>fst ` presented_rows R" if added_row: "(b,q)\<in>edit_rows (edit_added e)" for b q
  proof
    assume "b\<in>fst ` presented_rows R"
    then obtain g where g: "g\<in>set ?E" "b=?\<kappa> g" unfolding R_rows by auto
    obtain a where a: "a\<in>set ?new" "b=?\<kappa> a" using added_row unfolding A_rows by auto
    have "a=g" by (rule inj_onD[OF \<kappa>_inj]) (use a g in auto)
    then show False using a g by simp
  qed
  have applied: "presented_rows (edited_state R e)=(presented_rows R-edit_rows (edit_removed e))\<union>edit_rows (edit_added e)"
  proof -
    have "(presented_rows R-edit_rows (edit_removed e))\<union>edit_rows (edit_added e)=(?f ` set ?E-?f ` set ?gone)\<union>?f ` set ?new"
      by (simp only: R_rows D_rows A_rows)
    also have "\<dots>=?f ` ((set ?E-set ?gone)\<union>set ?new)"
      by (subst image_Un, subst inj_on_image_set_diff[OF f_inj]) auto
    also have "\<dots>=?f ` set ?E'" by (simp only: index)
    finally show ?thesis by (simp add: R'_rows)
  qed
  have sub: "edit_rows (edit_removed e)\<subseteq>presented_rows R" unfolding D_rows R_rows by auto
  show reduced: "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    using sub fresh applied by (simp add: edit_reduced_def)
  show "state_roots (edited_state R e)=state_roots R" by (simp add: edited_state_def)
  show "z\<in>presented_rows (edited_state R e)" if "z\<in>presented_rows R" "z\<notin>edit_rows (edit_removed e)" for z
    using that applied by simp
  show "a\<notin>fst ` set (state_atoms R)" if atom: "(a,n)\<in>set (edit_atoms e)" for a n
  proof
    assume "a\<in>fst ` set (state_atoms R)"
    then obtain j where j: "j<length ?names" "a=state_constant_key j" by (auto simp: R state_rows_of_def)
    obtain i where i: "length ?names\<le>i" "a=state_constant_key i" using atom by (auto simp: e)
    have "i=j" using i(2) j(2) injD[OF state_constant_key_injective] by simp
    then show False using i(1) j(1) by simp
  qed
  show "(development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
      \<in>set (state_entities (edited_state R e) (entity_kind_of g))"
    if "g\<in>set (snd (snd S))" "g\<in>set (snd (snd S'))" for g
  proof -
    have "g\<in>set ?E'" using that(2) by (simp add: S')
    then have "?f g\<in>set (state_entities (edited_state R e) (entity_kind_of g))" by (simp add: families')
    then show ?thesis using f_old[OF that(1)] by simp
  qed
  show "a\<notin>fst ` presented_rows (edited_state R e)" if removed_row: "(a,z)\<in>edit_rows (edit_removed e)" for a z
  proof
    assume "a\<in>fst ` presented_rows (edited_state R e)"
    then obtain z where z: "z\<in>presented_rows (edited_state R e)" "a=fst z" by (rule imageE)
    have "z\<in>?f ` set ?E'" using z(1) by (simp only: R'_rows)
    then obtain h where "h\<in>set ?E'" "z=?f h" by (rule imageE) (rule that)
    then have h: "h\<in>set ?E'" "a=?\<kappa> h" using z(2) by simp_all
    obtain d where d: "d\<in>set ?gone" "a=?\<kappa> d" using removed_row unfolding D_rows by auto
    have "d=h" by (rule inj_onD[OF \<kappa>_inj]) (use d h in auto)
    then show False using d h by auto
  qed
  show "b\<notin>fst ` presented_rows R" if "(b,q)\<in>edit_rows (edit_added e)" for b q
    using fresh[OF that] .
qed

text \<open>
  A further conclusion of the constructor that the contract's union of rows cannot give: a removed row of the
  edit is a row of its own kind's family in the request state.
\<close>

lemma state_edit_of_removed_within:
  assumes presented: "state_presenter S=Some R" and edit: "state_edit_of S ns removed added=Some e"
  shows "set (edit_removed e j)\<subseteq>set (state_entities R j)"
proof -
  have R: "R=state_rows_of S" using presented by (simp add: state_presenter_def split: if_splits)
  show ?thesis using edit by (auto simp: R state_rows_of_def state_edit_of_def Let_def split: if_splits)
qed

section \<open>A native answer carries its edit\<close>

text \<open>
  A native answer names its removed and added entities with the names it uses; its answer state appends
  those names to the request state's table and moves the entities into it
  (\<open>development_native_answer_state\<close>). That state is the edit applied, so the native answer's edit is the
  constructor at the moved entities, and the contract holds of the native answer's state with the edit read
  from the answer. The native answer is the contract's first instance; nothing of it is established again.
\<close>

definition development_native_answer_edit ::
    "isabelle_rooted_context \<Rightarrow> development_native_answer \<Rightarrow> state_edit option" where
  "development_native_answer_edit S A=(case A of (ns,removed,added) \<Rightarrow>
    let g=isabelle_state_embedding ns (isabelle_appended_names (fst (snd S)) ns) in
    state_edit_of S ns (map (isabelle_entity_rename g) removed) (map (isabelle_entity_rename g) added))"

lemma development_native_answer_state_applied:
  "development_native_answer_state S (ns,removed,added)=
    (let g=isabelle_state_embedding ns (isabelle_appended_names (fst (snd S)) ns) in
      edit_applied S ns (map (isabelle_entity_rename g) removed) (map (isabelle_entity_rename g) added))"
  by (simp add: development_native_answer_state_def edit_applied_def Let_def)

theorem development_native_answer_edit_refuses:
  "development_native_answer_edit S (ns,removed,added)=None \<longleftrightarrow>
    \<not>edit_specification_condition (snd (snd S)) (snd (snd (development_native_answer_state S (ns,removed,added))))"
  by (simp add: development_native_answer_edit_def development_native_answer_state_applied state_edit_of_refuses Let_def)

text \<open>
  A formed native answer keeps a presentable state presentable: the three conditions of
  \<open>development_native_answer_state_presentable\<close> are exactly \<open>state_presentable\<close>. Every consumer of the
  native answer's edit takes the constructor's contract through this corollary, once.
\<close>

corollary development_native_answer_presentable:
  assumes formed: "development_native_answer_formed A" and presentable: "state_presentable S"
  shows "state_presentable (development_native_answer_state S A)"
proof -
  have d: "distinct (fst (snd S))" and i: "state_positions S\<subseteq>{..<length (fst (snd S))}"
    and r: "distinct (map (isabelle_local_root (fst (snd S))) (fst S))"
    using presentable by (simp_all add: state_presentable_def)
  note answer=development_native_answer_state_presentable[OF formed d i r]
  show ?thesis unfolding state_presentable_def by (intro conjI answer)
qed

theorem development_native_answer_edit_contract:
  assumes read: "development_native_answer_read t=Some A" and presented: "state_presenter S=Some R"
    and edit: "development_native_answer_edit S A=Some e"
  shows "state_presents state_constant_key (development_native_answer_state S A) (edited_state R e)"
    and "keys_shared R (edited_state R e)"
    and "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))"
    and "state_roots (edited_state R e)=state_roots R"
    and "\<And>z. z\<in>presented_rows R \<Longrightarrow> z\<notin>edit_rows (edit_removed e) \<Longrightarrow> z\<in>presented_rows (edited_state R e)"
    and "\<And>a n. (a,n)\<in>set (edit_atoms e) \<Longrightarrow> a\<notin>fst ` set (state_atoms R)"
    and "\<And>g. g\<in>set (snd (snd S)) \<Longrightarrow> g\<in>set (snd (snd (development_native_answer_state S A))) \<Longrightarrow>
      (development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
        \<in>set (state_entities (edited_state R e) (entity_kind_of g))"
    and "\<And>a z. (a,z)\<in>edit_rows (edit_removed e) \<Longrightarrow> a\<notin>fst ` presented_rows (edited_state R e)"
    and "\<And>b q. (b,q)\<in>edit_rows (edit_added e) \<Longrightarrow> b\<notin>fst ` presented_rows R"
proof -
  obtain ns removed added where A: "A=(ns,removed,added)" by (cases A) auto
  let ?g="isabelle_state_embedding ns (isabelle_appended_names (fst (snd S)) ns)"
  have formed: "development_native_answer_formed A" using read by (simp add: development_native_answer_reads)
  have presentable: "state_presentable S" using presented by (simp add: state_presenter_def split: if_splits)
  have state: "development_native_answer_state S A=
      edit_applied S ns (map (isabelle_entity_rename ?g) removed) (map (isabelle_entity_rename ?g) added)"
    by (simp add: A development_native_answer_state_applied Let_def)
  have answer: "state_presentable (edit_applied S ns (map (isabelle_entity_rename ?g) removed)
      (map (isabelle_entity_rename ?g) added))"
    using development_native_answer_presentable[OF formed presentable] by (simp only: state)
  have edit': "state_edit_of S ns (map (isabelle_entity_rename ?g) removed) (map (isabelle_entity_rename ?g) added)=Some e"
    using edit by (simp add: A development_native_answer_edit_def Let_def)
  note contract=state_edit_contract[OF presented answer edit']
  show "state_presents state_constant_key (development_native_answer_state S A) (edited_state R e)"
    using contract(1) by (simp only: state)
  show "keys_shared R (edited_state R e)" by (rule contract(2))
  show "edit_reduced R (edited_state R e) (edit_rows (edit_removed e)) (edit_rows (edit_added e))" by (rule contract(3))
  show "state_roots (edited_state R e)=state_roots R" by (rule contract(4))
  show "z\<in>presented_rows (edited_state R e)" if "z\<in>presented_rows R" "z\<notin>edit_rows (edit_removed e)" for z
    by (rule contract(5)[OF that])
  show "a\<notin>fst ` set (state_atoms R)" if "(a,n)\<in>set (edit_atoms e)" for a n
    by (rule contract(6)[OF that])
  show "(development_entity_key (snd S) g,entity_row state_constant_key (snd S) g)
      \<in>set (state_entities (edited_state R e) (entity_kind_of g))"
    if "g\<in>set (snd (snd S))" "g\<in>set (snd (snd (development_native_answer_state S A)))" for g
    by (rule contract(7)[OF that(1) that(2)[unfolded state]])
  show "a\<notin>fst ` presented_rows (edited_state R e)" if "(a,z)\<in>edit_rows (edit_removed e)" for a z
    by (rule contract(8)[OF that])
  show "b\<notin>fst ` presented_rows R" if "(b,q)\<in>edit_rows (edit_added e)" for b q
    by (rule contract(9)[OF that])
qed

section \<open>The constructor looks entities up through an index of the request state's entities\<close>

text \<open>
  An answer's host work is its edit's, not its state's (design 171). The constructor's definition tests
  whole entities against whole lists; its code equations below look them up through indexes instead, and
  each is proved equal to the definition on the whole domain. An entity is keyed by its presentation, ordered
  (\<open>entity_order_key\<close>); the request state's entities are indexed once by their first positions
  (\<open>first_index_tree\<close>, the tree map's index read through the key, @{text first_index_carrier_index}),
  at the constructor's first argument, so that a stage judging several answers against one request state
  builds it once (@{text state_edit_of_indexed}). The removed and added entities are indexed by membership
  and by first position, duplicates are removed through the key's order (@{text entity_remdups_exact}), a
  kind's family is computed once (@{text kind_families_exact}), and the specification condition reads each
  state's development constants once (@{text edit_specification_condition_indexed}).
\<close>

definition entity_order_key :: "isabelle_entity \<Rightarrow> ordered_factor_term" where
  "entity_order_key e=Ordered_Factor_Term (isabelle_entity_data e)"

lemma entity_order_key_injective: "inj entity_order_key"
  by (rule injI) (auto simp: entity_order_key_def dest: injD[OF isabelle_entity_data_injective])

definition first_index_tree :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> ('k,nat) rbt" where
  "first_index_tree key xs=RBT.bulkload (zip (map key xs) [0..<length xs])"

lemma map_of_first_index:
  assumes key: "inj key"
  shows "map_of (zip (map key xs) [0..<length xs]) (key x)=value_reference_index x xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons y ys)
  have upto: "[0..<length (y#ys)]=0#map Suc [0..<length ys]"
    by (simp only: length_Cons map_Suc_upt upt_conv_Cons[OF zero_less_Suc])
  show ?case unfolding upto by (simp add: zip_map2 map_of_map Cons.IH inj_eq[OF key])
qed

lemma first_index_tree_lookup:
  assumes key: "inj key"
  shows "RBT.lookup (first_index_tree key xs) (key x)=value_reference_index x xs"
  by (simp add: first_index_tree_def RBT.lookup_bulkload map_of_first_index[OF key])

lemma first_index_tree_absent:
  assumes "k\<notin>range key"
  shows "RBT.lookup (first_index_tree key xs) k=None"
  using assms by (auto simp: first_index_tree_def RBT.lookup_bulkload map_of_eq_None_iff dest!: set_zip_leftD)

lemma first_index_tree_found:
  assumes key: "inj key"
  shows "RBT.lookup (first_index_tree key xs) (key x)=None \<longleftrightarrow> x\<notin>set xs"
  by (simp add: first_index_tree_lookup[OF key] value_reference_index_absent)

lemma first_index_image:
  "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)) \<longleftrightarrow>
    (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)"
proof
  assume "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))"
  then obtain x where x: "x\<in>set c" "k=key x" "v=the (value_reference_index x c)" by auto
  have "value_reference_index x c=Some v"
    using x value_reference_index_absent[of x c] by (cases "value_reference_index x c") auto
  then show "\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v" using x by auto
next
  assume "\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v"
  then obtain q where q: "k=key q" "value_reference_index q c=Some v" by auto
  have "q\<in>set c" using q(2) value_reference_index_absent[of q c] by auto
  then show "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))"
    using q by (auto simp: image_iff intro!: bexI[where x=q])
qed

text \<open>
  The index of a list by the first positions of its members is the tree map's index
  (@{thm [source] tree_map_carrier_index}) read through an injective key (@{thm [source] carrier_index_through_key}):
  its carrier is the relation of a member to its first position (@{const value_reference_index}). The tree the
  code builds, the bulkload of the keys zipped with their positions, has that index's lookups, since a bulkload
  keeps the first row at a key.
\<close>

lemma first_index_carrier_index:
  assumes key: "inj key"
  shows "carrier_index (\<lambda>xs x i. value_reference_index x xs=Some i) (\<lambda>_. True) UNIV key
    (first_index_tree key) tree_search"
proof -
  interpret through: carrier_index "\<lambda>xs x i. value_reference_index x xs=Some i" "\<lambda>_. True" UNIV key
    "\<lambda>c. RBT.bulkload (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c))" tree_search
  proof (rule carrier_index_through_key[OF tree_map_carrier_index])
    show "distinct (map fst (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)))" for c
      using inj_on_subset[OF key] by (simp add: distinct_map o_def)
    show "(k,v)\<in>set (map (\<lambda>x. (key x,the (value_reference_index x c))) (remdups c)) \<longleftrightarrow>
        (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)" for c k v
      by (rule first_index_image)
    show "inj_on key UNIV" by (rule key)
  qed
  show ?thesis
  proof (rule carrier_index.intro)
    show "inj_on key UNIV" by (rule key)
    fix c k v
    show "tree_search (first_index_tree key c) k v \<longleftrightarrow> (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)"
    proof (cases "k\<in>range key")
      case True
      then obtain x where k: "k=key x" by auto
      have "tree_search (first_index_tree key c) k v \<longleftrightarrow> value_reference_index x c=Some v"
        by (simp add: k first_index_tree_lookup[OF key])
      also have "\<dots> \<longleftrightarrow> (\<exists>q\<in>UNIV. key q=k \<and> value_reference_index q c=Some v)"
        using through.represents[where c=c and k=k and v=v] through.query_search[where c=c and q=x and v=v]
        by (simp add: k)
      finally show ?thesis .
    next
      case False
      then show ?thesis by (auto simp: first_index_tree_absent)
    qed
  qed
qed

lemma member_tree_key_found:
  assumes key: "inj key"
  shows "RBT.lookup (ordered_member_tree (fset_of_list (map key xs))) (key x)\<noteq>None \<longleftrightarrow> x\<in>set xs"
  using listed_member_lookup[of "map key xs" "key x"] inj_image_mem_iff[OF key] by simp

lemma member_tree_key_absent:
  assumes key: "inj key"
  shows "RBT.lookup (ordered_member_tree (fset_of_list (map key xs))) (key x)=None \<longleftrightarrow> x\<notin>set xs"
  using member_tree_key_found[OF key] by blast

lemma listed_member_absent: "RBT.lookup (ordered_member_tree (fset_of_list xs)) x=None \<longleftrightarrow> x\<notin>set xs"
  using listed_member_lookup by blast

text \<open>A list whose members carry their keys is filtered by the keys, which are computed once.\<close>

definition keyed_filter :: "('k \<Rightarrow> bool) \<Rightarrow> ('a\<times>'k) list \<Rightarrow> 'a list" where
  "keyed_filter Q EK=map fst (filter (\<lambda>p. Q (snd p)) EK)"

lemma keyed_filter_map: "keyed_filter Q (map (\<lambda>e. (e,key e)) E)=filter (\<lambda>e. Q (key e)) E"
  by (induction E) (simp_all add: keyed_filter_def)

lemma list_all_specification_constants:
  "list_all P (concat (map (\<lambda>e. case e of Isabelle_Specification p \<Rightarrow> isabelle_term_constants p | _ \<Rightarrow> []) E))=
    list_all (\<lambda>e. case e of Isabelle_Specification p \<Rightarrow> list_all P (isabelle_term_constants p) | _ \<Rightarrow> True) E"
proof (induction E)
  case Nil
  show ?case by simp
next
  case (Cons e E)
  then show ?case by (cases e) simp_all
qed

lemma value_reference_index_append_absent:
  "x\<notin>set xs \<Longrightarrow> value_reference_index x (xs@ys)=map_option ((+) (length xs)) (value_reference_index x ys)"
proof (induction xs)
  case Nil
  show ?case by (cases "value_reference_index x ys") simp_all
next
  case (Cons y xs)
  then show ?case by (cases "value_reference_index x ys") simp_all
qed

subsection \<open>Duplicates are removed through the key's order\<close>

lemma remdups_map_injective:
  assumes "inj_on f (set xs)"
  shows "remdups (map f xs)=map f (remdups xs)"
proof -
  have d: "distinct (map f (remdups xs))" using assms by (simp add: distinct_map)
  show ?thesis using remdups_map_remdups[of f xs] distinct_remdups_id[OF d] by simp
qed

lemma zip_key_lookup:
  assumes key: "inj key" and member: "x\<in>set xs"
  shows "map_of (zip (map key xs) xs) (key x)=Some x"
  using member by (induction xs) (auto simp: inj_eq[OF key])

definition entity_remdups :: "isabelle_entity list \<Rightarrow> isabelle_entity list" where
  "entity_remdups xs=(let T=RBT.bulkload (zip (map entity_order_key xs) xs) in
    map (\<lambda>k. the (RBT.lookup T k)) (ordered_remdups (map entity_order_key xs)))"

lemma entity_remdups_exact: "entity_remdups xs=remdups xs"
proof -
  have inj: "inj_on entity_order_key (set xs)" by (rule inj_on_subset[OF entity_order_key_injective]) simp
  show ?thesis
    by (simp add: entity_remdups_def Let_def ordered_remdups_exact remdups_map_injective[OF inj] RBT.lookup_bulkload)
      (rule map_idI, simp add: zip_key_lookup[OF entity_order_key_injective])
qed

subsection \<open>A kind's family is computed once\<close>

definition kind_families :: "(isabelle_entity \<Rightarrow> 'b) \<Rightarrow> isabelle_entity list \<Rightarrow> entity_kind \<Rightarrow> 'b list" where
  "kind_families f xs=(let fam=(\<lambda>k. map f (filter (\<lambda>y. entity_kind_of y=k) xs));
     fb=fam Base_Kind; fv=fam Development_Kind; fr=fam Frontier_Kind; fd=fam Definition_Kind;
     fs=fam Specification_Kind; fq=fam Equation_Kind in
     (\<lambda>k. case k of Base_Kind \<Rightarrow> fb | Development_Kind \<Rightarrow> fv | Frontier_Kind \<Rightarrow> fr
       | Definition_Kind \<Rightarrow> fd | Specification_Kind \<Rightarrow> fs | Equation_Kind \<Rightarrow> fq))"

lemma kind_families_exact: "kind_families f xs=(\<lambda>k. map f (filter (\<lambda>d. entity_kind_of d=k) xs))"
  by (rule ext) (simp add: kind_families_def Let_def split: entity_kind.split)

lemma appended_atoms:
  "map (\<lambda>(i,n). (state_constant_key i,n)) (zip [m..<length xs] (drop m xs))=
    map (\<lambda>i. (state_constant_key i,xs!i)) [m..<length xs]"
  by (rule nth_equalityI) (simp_all add: nth_zip)

text \<open>
  An added entity is new to the request state, so its first position in the request state followed by the
  added entities is its first position among the added ones, after every entity of the request state.
\<close>

lemma added_keys:
  "map (\<lambda>a. (first_occurrence_key (E@A) a,g a)) (filter P (remdups (filter (\<lambda>a. a\<notin>set E) A)))=
    map (\<lambda>a. (natural_binary_digits (case value_reference_index a A of
      None \<Rightarrow> length E+length A | Some j \<Rightarrow> length E+j),g a)) (filter P (remdups (filter (\<lambda>a. a\<notin>set E) A)))"
  by (rule map_cong[OF refl])
    (simp add: first_occurrence_key_def value_reference_index_append_absent o_def split: option.split)

lemma removed_keys:
  "natural_binary_digits (case value_reference_index d E of None \<Rightarrow> length E | Some i \<Rightarrow> i)=first_occurrence_key E d"
  by (simp add: first_occurrence_key_def)

subsection \<open>The code equations\<close>

lemma isabelle_appended_names_indexed [code]:
  "isabelle_appended_names names=(let T=ordered_member_tree (fset_of_list names) in
    (\<lambda>ns. names@filter (\<lambda>n. RBT.lookup T n=None) ns))"
  by (simp add: fun_eq_iff isabelle_appended_names_def Let_def listed_member_absent)

lemma edit_applied_indexed [code]:
  "edit_applied S ns removed added=(let Rm=ordered_member_tree (fset_of_list (map entity_order_key removed)) in
    (fst S,(isabelle_appended_names (fst (snd S)) ns,
      filter (\<lambda>e. RBT.lookup Rm (entity_order_key e)=None) (snd (snd S))@added)))"
  by (simp only: edit_applied_def Let_def member_tree_key_absent[OF entity_order_key_injective])

lemma edit_specification_condition_indexed [code]:
  "edit_specification_condition E=(let D=ordered_member_tree (fset_of_list (isabelle_development_constants E));
     C=concat (map (\<lambda>e. case e of Isabelle_Specification p \<Rightarrow> isabelle_term_constants p | _ \<Rightarrow> []) E) in
     (\<lambda>E'. let D'=ordered_member_tree (fset_of_list (isabelle_development_constants E')) in
       list_all (\<lambda>c. (RBT.lookup D c\<noteq>None)=(RBT.lookup D' c\<noteq>None)) C))"
  by (intro ext) (simp only: edit_specification_condition_def Let_def listed_member_lookup
      list_all_specification_constants)

lemma entity_row_shared [code]:
  "entity_row key C=(let D=isabelle_development_constants (snd C) in
    (\<lambda>e. \<lparr>row_declared=map key (entity_declared e),
      row_subjects=map key (isabelle_entity_subjects (fst C) D e),
      row_mentions=map key (entity_mentions e),
      row_identity=isabelle_local_entities (fst C) [e]\<rparr>))"
  by (simp add: fun_eq_iff entity_row_def Let_def)

lemma state_edit_of_indexed [code]:
  "state_edit_of S=(let E=snd (snd S); names=fst (snd S); T=first_index_tree entity_order_key E;
     EK=map (\<lambda>e. (e,entity_order_key e)) E; appended=isabelle_appended_names names;
     condition=edit_specification_condition E;
     key=(\<lambda>d. natural_binary_digits (case RBT.lookup T (entity_order_key d) of None \<Rightarrow> length E | Some i \<Rightarrow> i));
     row=entity_row state_constant_key (snd S) in
     (\<lambda>ns removed added. let Rm=ordered_member_tree (fset_of_list (map entity_order_key removed));
       S'=(fst S,(appended ns,keyed_filter (\<lambda>k. RBT.lookup Rm k=None) EK@added)); names'=fst (snd S');
       Ta=first_index_tree entity_order_key added;
       gone=entity_remdups (keyed_filter (\<lambda>k. RBT.lookup Rm k\<noteq>None \<and> RBT.lookup Ta k=None) EK);
       new=entity_remdups (filter (\<lambda>a. RBT.lookup T (entity_order_key a)=None) added);
       key'=(\<lambda>a. natural_binary_digits (case RBT.lookup Ta (entity_order_key a) of
         None \<Rightarrow> length E+length added | Some j \<Rightarrow> length E+j));
       row'=entity_row state_constant_key (snd S') in
     if condition (snd (snd S')) then
       Some \<lparr>edit_atoms=map (\<lambda>(i,n). (state_constant_key i,n))
           (zip [length names..<length names'] (drop (length names) names')),
         edit_removed=kind_families (\<lambda>d. (key d,row d)) gone,
         edit_added=kind_families (\<lambda>a. (key' a,row' a)) new\<rparr>
     else None))"
  unfolding Let_def keyed_filter_map member_tree_key_found[OF entity_order_key_injective]
    member_tree_key_absent[OF entity_order_key_injective] first_index_tree_lookup[OF entity_order_key_injective]
  by (intro ext) (simp add: state_edit_of_def Let_def edit_applied_def appended_atoms entity_remdups_exact kind_families_exact
      value_reference_index_absent development_entity_key_def removed_keys added_keys)

end
