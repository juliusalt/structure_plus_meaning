theory Development_Edited_Reach
  imports Development_Verdict_Unreached Development_Edited_Local
begin

section \<open>The field \<open>unreached\<close> of an answer state, read from its request state and the edit\<close>

text \<open>
  Design 171's build 5, its state half. The answer state's reach is recomputed from what the edit's removed
  rows reach: a key set \<open>O\<close>, produced by an executor and admitted here natively by two readings, holds the
  target of every edge the edit removes and is closed under the request state's successors. Then every key
  the request state reaches outside \<open>O\<close> is reached in the answer state (the removal lemma of
  \<open>Native_Table_Reach\<close>), and \<open>unreached\<close> is read over the answer table seeded with such keys and restricted
  to the keys the evaluation can visit, at the added families and the rows of the answer state at a key of
  \<open>O\<close>. No program reads \<open>unreached\<close> again: its call is \<open>native_unreached_rows\<close>'s at other arguments.

  The seeds are not every key of the request table: that table holds a row at every atom of the name
  table, and an atom no root heads and no row declares or mentions is a key no closed state reaches. The
  seeds are the keys that are the one key of some row, and the root keys (\<open>state_reach_seeds\<close>); a closed
  state reaches each. A smaller seed set costs work and never truth, as a larger \<open>O\<close> does.
\<close>

section \<open>Two rearranging rules and two readings of their own\<close>

text \<open>
  A rotation passes a call's element beside its context in the order a callee reads them: the element of a
  traversal over keys becomes the key of a keyed call.
\<close>

definition native_rotate_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_rotate_rule r=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))
    [([0],(r,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 0)) (native_var 1)))]"

locale native_rotate_program = native_rule_family P s "[([0],native_rotate_rule r)]"
  for P :: "'u native_system" and s r :: "'u definition_site"

sublocale native_rotate_program \<subseteq> rearranged: native_rearranging_program P s
  "Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)" r
  "Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 0)) (native_var 1)"
  unfolding native_rearranging_program_def native_rearranging_program_axioms_def
  using native_rule_family_axioms[unfolded native_rotate_rule_def] by auto

context native_rotate_program
begin

theorem exact:
  "(s,Pair_Term (Pair_Term a b) c)\<in>positive_meaning P \<longleftrightarrow> (r,Pair_Term (Pair_Term c a) b)\<in>positive_meaning P"
  using rearranged.at[of "native_values [a,b,c]"] by simp

end

text \<open>A row mentions the key given as its context: the mentions list searched by membership.\<close>

locale row_mentioned_program = mentions: row_mentions_program P r m + members: native_member_program P m
  for P :: "'u native_system" and r m :: "'u definition_site"
begin

theorem exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(r,Pair_Term (path_term c) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow> c\<in>set (row_mentions (snd z))"
  by (simp add: mentions.exact[OF identity] keys_term_def members.exact)

end

text \<open>
  A mention is found in a store, or it is kept: two rules at one site. The first reads the store beside the
  mention, the second passes the mention to a callee with the rest of the context.
\<close>

definition mention_found_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "mention_found_rule m=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition mention_kept_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "mention_kept_rule u=finite_native_rule
    (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3)))
      (native_var 2))
    [([0],(u,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 1)) (native_var 3)))]"

definition mention_kept_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "mention_kept_rules m u=[([0],mention_found_rule m),([1],mention_kept_rule u)]"

definition mention_kept_listing :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>local_address finite_term_pattern\<times>
      (local_address\<times>('u definition_site\<times>local_address finite_term_pattern)) list) list" where
  "mention_kept_listing m u=
    [([0],Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2),
      [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]),
     ([1],Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3)))
      (native_var 2),[([0],(u,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 1)) (native_var 3)))])]"

lemma mention_kept_rules_listing: "mention_kept_rules m u=native_rule_listing (mention_kept_listing m u)"
  by (simp add: mention_kept_rules_def mention_kept_listing_def native_rule_listing_def mention_found_rule_def
    mention_kept_rule_def)

locale mention_kept_program = native_rule_family P w "mention_kept_rules m u"
  for P :: "'u native_system" and w m u :: "'u definition_site"
begin

sublocale triples: native_listed_law P w "mention_kept_listing m u"
  unfolding native_listed_law_def mention_kept_rules_listing[symmetric] by (rule native_rule_family_axioms)

theorem exact:
  assumes xf: "term_formed x" and yf: "term_formed y" and sf: "term_formed ss"
  shows "(w,Pair_Term (Pair_Term x (Pair_Term y ss)) c)\<in>positive_meaning P \<longleftrightarrow>
    (m,Pair_Term x c)\<in>positive_meaning P \<or> (u,Pair_Term (Pair_Term c y) ss)\<in>positive_meaning P"
proof
  assume holds: "(w,Pair_Term (Pair_Term x (Pair_Term y ss)) c)\<in>positive_meaning P"
  obtain d p ps f where rule: "(d,p,ps)\<in>set (mention_kept_listing m u)"
    and shape: "evaluate_pattern f (decode_finite_pattern p)=Pair_Term (Pair_Term x (Pair_Term y ss)) c"
    and support: "\<forall>(k,e,q)\<in>set ps. (e,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
    by (rule triples.holds_triple[OF holds]) (rule that; assumption)
  from rule consider (found) "p=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2)"
      "ps=[([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"
    | (kept) "p=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
        (Finite_Pattern_Pair (native_var 1) (native_var 3))) (native_var 2)"
      "ps=[([0],(u,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 1)) (native_var 3)))]"
    by (auto simp: mention_kept_listing_def)
  then show "(m,Pair_Term x c)\<in>positive_meaning P \<or> (u,Pair_Term (Pair_Term c y) ss)\<in>positive_meaning P"
  proof cases
    case found
    have premise: "(m,Pair_Term (f [0]) (f [2]))\<in>positive_meaning P" using support found(2) by simp
    have "f [0]=x" "f [2]=c" using shape by (simp_all add: found(1))
    then show ?thesis using premise by simp
  next
    case kept
    have premise: "(u,Pair_Term (Pair_Term (f [2]) (f [1])) (f [3]))\<in>positive_meaning P" using support kept(2) by simp
    have "f [1]=y" "f [2]=c" "f [3]=ss" using shape by (simp_all add: kept(1))
    then show ?thesis using premise by simp
  qed
next
  assume "(m,Pair_Term x c)\<in>positive_meaning P \<or> (u,Pair_Term (Pair_Term c y) ss)\<in>positive_meaning P"
  then show "(w,Pair_Term (Pair_Term x (Pair_Term y ss)) c)\<in>positive_meaning P"
  proof
    assume found: "(m,Pair_Term x c)\<in>positive_meaning P"
    have cf: "term_formed c" using positive_meaning_term_formed[OF found] by simp
    have "(w,evaluate_pattern (native_values [x,Pair_Term y ss,c]) (decode_finite_pattern
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2))))\<in>positive_meaning P"
      by (rule triples.step_triple[where c="[0]" and ps="[([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
        (use found cf xf yf sf in \<open>simp_all add: mention_kept_listing_def\<close>)
    then show ?thesis by simp
  next
    assume kept: "(u,Pair_Term (Pair_Term c y) ss)\<in>positive_meaning P"
    have cf: "term_formed c" using positive_meaning_term_formed[OF kept] by simp
    have "(w,evaluate_pattern (native_values [x,y,c,ss]) (decode_finite_pattern
        (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3)))
          (native_var 2))))\<in>positive_meaning P"
      by (rule triples.step_triple[where c="[1]" and
          ps="[([0],(u,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 2) (native_var 1)) (native_var 3)))]"])
        (use kept cf xf yf sf in \<open>simp_all add: mention_kept_listing_def\<close>)
    then show ?thesis by simp
  qed
qed

end

text \<open>
  The row reading of \<open>O\<close>'s targets passes a row's subjects and mentions to the traversal over its mentions,
  with the store of \<open>O\<close> and the answer state's subject indexes as context.
\<close>

definition target_row_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "target_row_rule t=finite_native_rule
    (row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3) (native_var 4)
      (native_var 5) (native_var 6))
    [([0],(t,Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4)))
      (native_var 5)))]"

section \<open>The admission program\<close>

text \<open>
  The program holds the mentions program, so \<open>O\<close>'s closure is \<open>excess\<close>'s reading at \<open>O\<close>'s keys, the
  list, at \<open>excess\<close>'s own sites, and the targets reading beside it, which reads \<open>O\<close> as the same list: a
  mention is in \<open>O\<close> through the list checker's test, and a row mentions a key through its membership, held
  once at @{text verdict_row_member}.
\<close>

abbreviation removal_key_call :: "local_address option definition_site" where
  "removal_key_call \<equiv> (Some [],[40])"
abbreviation removal_closure :: "local_address option definition_site" where
  "removal_closure \<equiv> (Some [],[41])"

abbreviation removal_row_mentions :: "local_address option definition_site" where
  "removal_row_mentions \<equiv> (Some [],[43])"
abbreviation removal_fibre_some :: "local_address option definition_site" where
  "removal_fibre_some \<equiv> (Some [],[44])"
abbreviation removal_search :: "local_address option definition_site" where
  "removal_search \<equiv> (Some [],[45])"
abbreviation removal_index_call :: "local_address option definition_site" where
  "removal_index_call \<equiv> (Some [],[46])"
abbreviation removal_families_some :: "local_address option definition_site" where
  "removal_families_some \<equiv> (Some [],[47])"
abbreviation removal_subject_call :: "local_address option definition_site" where
  "removal_subject_call \<equiv> (Some [],[48])"
abbreviation removal_subjects :: "local_address option definition_site" where
  "removal_subjects \<equiv> (Some [],[49])"
abbreviation removal_mention :: "local_address option definition_site" where
  "removal_mention \<equiv> (Some [],[50])"
abbreviation removal_mentions :: "local_address option definition_site" where
  "removal_mentions \<equiv> (Some [],[51])"
abbreviation removal_target_row :: "local_address option definition_site" where
  "removal_target_row \<equiv> (Some [],[52])"
abbreviation removal_target_family :: "local_address option definition_site" where
  "removal_target_family \<equiv> (Some [],[53])"
abbreviation removal_targets :: "local_address option definition_site" where
  "removal_targets \<equiv> (Some [],[54])"


definition edited_reach_definitions :: "(local_address option definition_site\<times>
    (local_address\<times>(local_address,local_address,local_address option definition_site) finite_factor_schema) list) list" where
  "edited_reach_definitions=verdict_mentions_definitions@[
    (removal_key_call,[([0],native_rotate_rule verdict_excess)]),
    (removal_closure,native_every_rules removal_closure removal_key_call),
    (removal_row_mentions,[([0],row_mentions_rule verdict_row_member)]),
    (removal_fibre_some,native_some_rules removal_fibre_some removal_row_mentions),
    (removal_search,native_store_search_rules removal_search removal_fibre_some),
    (removal_index_call,[([0],subject_call_rule removal_search)]),
    (removal_families_some,native_some_rules removal_families_some removal_index_call),
    (removal_subject_call,[([0],native_rotate_rule removal_families_some)]),
    (removal_subjects,native_every_rules removal_subjects removal_subject_call),
    (removal_mention,mention_kept_rules verdict_key_cited removal_subjects),
    (removal_mentions,native_every_rules removal_mentions removal_mention),
    (removal_target_row,[([0],target_row_rule removal_mentions)]),
    (removal_target_family,native_every_rules removal_target_family removal_target_row),
    (removal_targets,native_every_rules removal_targets removal_target_family)]"

definition finite_edited_reach :: "local_address option finite_native_system" where
  "finite_edited_reach=finite_rule_program edited_reach_definitions"

definition edited_reach_system :: "local_address option native_system" where
  "edited_reach_system=decode_finite_system finite_edited_reach"

lemma finite_edited_reach_formed: "finite_system_formed finite_edited_reach"
  by code_simp

lemma edited_reach_formed: "schema_system_formed edited_reach_system"
  using finite_edited_reach_formed by (simp only: edited_reach_system_def finite_system_formed_correct)

lemma edited_reach_family:
  assumes member: "(d,rs)\<in>set edited_reach_definitions"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family edited_reach_system d rs"
  unfolding edited_reach_system_def finite_edited_reach_def
  by (rule finite_rule_program_family[OF edited_reach_formed[unfolded edited_reach_system_def
      finite_edited_reach_def] _ member plain]) (simp add: edited_reach_definitions_def verdict_mentions_definitions_def)

lemmas edited_reach_rule_defs = edited_reach_definitions_def verdict_mentions_rule_defs
  native_member_rules_def native_member_here_def native_member_later_def native_some_rules_def
  native_some_first_def native_rotate_rule_def mention_kept_rules_def
  mention_found_rule_def mention_kept_rule_def target_row_rule_def

lemma edited_reach_distinct: "distinct (map fst edited_reach_definitions)"
  by code_simp

text \<open>
  The sites of the mentions program keep their meanings in the admission program: the join law of rule
  programs (@{thm finite_rule_program_join}), consumed once.
\<close>

lemma edited_reach_mentions_field:
  assumes site: "d\<in>fst ` set verdict_mentions_definitions"
  shows "(d,t)\<in>positive_meaning edited_reach_system \<longleftrightarrow> (d,t)\<in>positive_meaning verdict_mentions_system"
  unfolding edited_reach_system_def finite_edited_reach_def verdict_mentions_system_def finite_verdict_mentions_def
  by (rule finite_rule_program_join[OF edited_reach_formed[unfolded edited_reach_system_def
    finite_edited_reach_def] edited_reach_distinct verdict_mentions_formed[unfolded verdict_mentions_system_def
    finite_verdict_mentions_def]]) (use site in \<open>auto simp: edited_reach_definitions_def\<close>)

interpretation removal_key_calls: native_rotate_program edited_reach_system removal_key_call verdict_excess
  unfolding native_rotate_program_def by (rule edited_reach_family) (simp_all add: edited_reach_rule_defs)

interpretation removal_closures: native_every_program edited_reach_system removal_closure removal_key_call
  unfolding native_every_program_def by (rule edited_reach_family) (simp_all add: edited_reach_rule_defs)

section \<open>\<open>O\<close>'s closure\<close>

lemma key_index_term_formed:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "term_formed (key_index_term rd ident A F)"
  unfolding key_index_term_def by (rule store_term_formed, rule state_family_term_formed, rule identity)

lemma key_indexes_term_formed:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "term_formed (key_indexes_term rd ident A Fs)"
  unfolding key_indexes_term_def by (simp add: data_list_term_formed key_index_term_formed[OF identity])

text \<open>
  \<open>O\<close> is closed when every row of the request state about a key of \<open>O\<close> has every mention in \<open>O\<close>: at each
  key of \<open>O\<close>, \<open>excess\<close>'s reading at \<open>O\<close>'s own store, over the subject index at \<open>O\<close>'s keys.
\<close>

theorem native_closure_exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(removal_closure,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident L Fs)) (keys_term L))
      \<in>positive_meaning edited_reach_system \<longleftrightarrow>
    (\<forall>a\<in>set L. \<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow> set (row_mentions (snd z))\<subseteq>set L)"
proof -
  have site: "verdict_excess\<in>fst ` set verdict_mentions_definitions"
    by (simp add: verdict_mentions_definitions_def)
  have "(removal_closure,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident L Fs))
      (data_list_term (map path_term L)))\<in>positive_meaning edited_reach_system \<longleftrightarrow>
    (\<forall>a\<in>set L. (verdict_excess,Pair_Term (Pair_Term (path_term a) (keys_term L)) (subject_indexes_term ident L Fs))
      \<in>positive_meaning verdict_mentions_system)"
    by (simp add: removal_closures.exact removal_key_calls.exact key_indexes_term_formed[OF identity]
      keys_term_formed edited_reach_mentions_field[OF site])
  also have "\<dots> \<longleftrightarrow> (\<forall>a\<in>set L. \<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L)"
    by (simp add: native_excess_rows[OF identity])
  finally show ?thesis by (simp only: keys_term_def[of L])
qed

section \<open>\<open>O\<close>'s targets\<close>

text \<open>
  A row's mention is kept when, for every subject of the row, some row of the answer state about that subject
  mentions it; a removed row's targets are admitted when each of its mentions is in \<open>O\<close> or is kept.
\<close>

definition edited_target :: "state_key list \<Rightarrow> state_key list \<Rightarrow> 'i state_family list \<Rightarrow>
    state_key\<times>'i state_row \<Rightarrow> bool" where
  "edited_target L A Fs z \<longleftrightarrow> (\<forall>c\<in>set (row_mentions (snd z)). c\<in>set L \<or>
    (\<forall>s\<in>set (row_subjects (snd z)). s\<in>set A \<and>
      (\<exists>F\<in>set Fs. \<exists>z'\<in>set F. s\<in>set (row_subjects (snd z')) \<and> c\<in>set (row_mentions (snd z')))))"

text \<open>
  The targets reading is a notion of its own: a locale whose parameters are its sites, composed of the
  collection notions it reads, so a program holding it at other sites consumes its \<open>exact\<close> and
  proves nothing of it again. \<open>edited_reach_system\<close> holds it at sites 43\<dash>54, with the list checker's
  test at 19 and its membership at 11 (\<open>removal_targets_program\<close>).
\<close>

locale edited_targets_program =
    rows: row_mentioned_program P rw m + fibres: native_some_program P fs rw +
    searches: native_store_search_program P sr fs +
    index_calls: subject_call_program P ic sr +
    families: native_some_program P fa ic + subject_calls: native_rotate_program P sc fa +
    subject_lists: native_every_program P su sc + founds: list_cited_program P kf m +
    kept: mention_kept_program P mo kf su + mention_lists: native_every_program P ml mo +
    target_rows: native_rearranging_program P tr
      "row_pattern (Finite_Pattern_Pair (native_var 0) (native_var 1)) (native_var 2) (native_var 3) (native_var 4)
        (native_var 5) (native_var 6)" ml
      "Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 4)))
        (native_var 5)" +
    target_families: native_every_program P tf tr + target_selections: native_every_program P ts tf
  for P :: "'u native_system" and ts tf tr ml mo kf su sc fa ic sr fs rw m :: "'u definition_site" +
  fixes ident :: "'i \<Rightarrow> factor_term"
  assumes identity: "\<And>y. term_formed (ident y)"
begin

lemma fibre_exact:
  "(fs,Pair_Term (path_term c) (state_family_term ident F))\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>z\<in>set F. c\<in>set (row_mentions (snd z)))"
  by (simp add: state_family_term_def fibres.exact rows.exact[OF identity]
      state_row_term_formed[OF identity])

sublocale reading: key_index_reading P sr fs path_term ident "\<lambda>c F. \<exists>z\<in>set F. c\<in>set (row_mentions (snd z))"
    row_subjects
  by unfold_locales (simp_all add: identity fibre_exact)

lemma families_exact:
  "(fa,Pair_Term (Pair_Term (path_term s) (path_term c)) (key_indexes_term row_subjects ident A Fs))
      \<in>positive_meaning P \<longleftrightarrow>
    s\<in>set A \<and> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. s\<in>set (row_subjects (snd z)) \<and> c\<in>set (row_mentions (snd z)))"
  by (auto simp: key_indexes_term_def families.exact index_calls.call_exact reading.fibre_exact Bex_def
      key_fibre_member key_index_term_formed[OF identity]; force)

lemma subjects_exact:
  "(su,Pair_Term (Pair_Term (path_term c) (key_indexes_term row_subjects ident A Fs)) (keys_term ss))
      \<in>positive_meaning P \<longleftrightarrow>
    (\<forall>s\<in>set ss. s\<in>set A \<and> (\<exists>F\<in>set Fs. \<exists>z\<in>set F. s\<in>set (row_subjects (snd z)) \<and> c\<in>set (row_mentions (snd z))))"
  by (subst keys_term_def[of ss]) (simp add: subject_lists.exact subject_calls.exact
      families_exact key_indexes_term_formed[OF identity])

lemma mention_exact:
  "(mo,Pair_Term (Pair_Term (keys_term L) (Pair_Term (key_indexes_term row_subjects ident A Fs)
      (keys_term ss))) (path_term c))\<in>positive_meaning P \<longleftrightarrow>
    c\<in>set L \<or> (\<forall>s\<in>set ss. s\<in>set A \<and>
      (\<exists>F\<in>set Fs. \<exists>z\<in>set F. s\<in>set (row_subjects (snd z)) \<and> c\<in>set (row_mentions (snd z))))"
proof -
  have found: "(kf,Pair_Term (keys_term L) (path_term c))\<in>positive_meaning P \<longleftrightarrow> c\<in>set L"
    by (rule founds.exact)
  show ?thesis
    by (simp add: kept.exact[OF keys_term_formed key_indexes_term_formed[OF identity]
        keys_term_formed] found subjects_exact)
qed

lemma mentions_exact:
  "(ml,Pair_Term (Pair_Term (keys_term L) (Pair_Term (key_indexes_term row_subjects ident A Fs)
      (keys_term ss))) (keys_term ms))\<in>positive_meaning P \<longleftrightarrow>
    (\<forall>c\<in>set ms. c\<in>set L \<or> (\<forall>s\<in>set ss. s\<in>set A \<and>
      (\<exists>F\<in>set Fs. \<exists>z\<in>set F. s\<in>set (row_subjects (snd z)) \<and> c\<in>set (row_mentions (snd z)))))"
  by (subst keys_term_def[of ms]) (simp add: mention_lists.exact mention_exact
      key_indexes_term_formed[OF identity])

lemma target_row_exact:
  "(tr,Pair_Term (Pair_Term x I) (state_row_term ident z))\<in>positive_meaning P \<longleftrightarrow>
    (ml,Pair_Term (Pair_Term x (Pair_Term I (keys_term (row_subjects (snd z)))))
      (keys_term (row_mentions (snd z))))\<in>positive_meaning P"
  using target_rows.at[of "native_values [x,I,path_term (fst z),keys_term (row_declared (snd z)),
      keys_term (row_subjects (snd z)),keys_term (row_mentions (snd z)),ident (row_identity (snd z))]"]
  by (simp add: row_pattern_def state_row_term_def identity insert_Diff_if)

theorem exact:
  "(ts,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident A Fs)) (state_families_term ident Ds))
      \<in>positive_meaning P \<longleftrightarrow> (\<forall>D\<in>set Ds. \<forall>z\<in>set D. edited_target L A Fs z)"
  by (simp add: state_families_term_def state_family_term_def target_selections.exact
      target_families.exact target_row_exact mentions_exact edited_target_def
      key_indexes_term_formed[OF identity])

end

lemma removal_targets_program:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "edited_targets_program edited_reach_system removal_targets removal_target_family removal_target_row
    removal_mentions removal_mention verdict_key_cited removal_subjects
    removal_subject_call removal_families_some removal_index_call removal_search removal_fibre_some
    removal_row_mentions verdict_row_member ident"
  unfolding edited_targets_program_def edited_targets_program_axioms_def row_mentioned_program_def row_mentions_program_def
    native_member_program_def native_some_program_def native_store_search_program_def
    native_rearranging_program_def native_rearranging_program_axioms_def native_rotate_program_def
    native_every_program_def list_cited_program_def native_swap_program_def mention_kept_program_def
    subject_call_program_def
  by (intro conjI allI; (rule edited_reach_family | rule identity)?)
    (simp_all add: edited_reach_rule_defs row_pattern_def subject_call_rule_def)

theorem native_targets_exact:
  assumes identity: "\<And>y. term_formed (ident y)"
  shows "(removal_targets,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident A Fs))
      (state_families_term ident Ds))\<in>positive_meaning edited_reach_system \<longleftrightarrow>
    (\<forall>D\<in>set Ds. \<forall>z\<in>set D. edited_target L A Fs z)"
  by (rule edited_targets_program.exact[OF removal_targets_program[OF identity]])

section \<open>An admitted \<open>O\<close> meets the removal lemma's premises\<close>

lemma state_reach_table_edges:
  "(p,k)\<in>reach_edges (state_reach_table As Rs Fs) \<longleftrightarrow> k\<in>fst ` set As \<and>
    (\<exists>F\<in>set Fs. \<exists>z\<in>set F. k\<in>set (row_mentions (snd z)) \<and> p\<in>set (row_subjects (snd z)))"
  by (auto simp: reach_edges_member state_reach_table_row state_reach_predecessors_member)

lemma state_reach_table_roots:
  "reach_roots (state_reach_table As Rs Fs)={k. k\<in>fst ` set As \<and> k\<in>set (state_root_keys Rs)}"
  by (auto simp: reach_roots_def state_reach_table_row)

lemma removal_closure_edges:
  assumes closure: "\<forall>a\<in>set L. \<forall>F\<in>set Fs. \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L"
    and edge: "(p,k)\<in>reach_edges (state_reach_table As Rs Fs)" and source: "p\<in>set L"
  shows "k\<in>set L"
  using edge closure source by (auto simp: state_reach_table_edges)

lemma removal_targets_edges:
  assumes targets: "\<forall>D\<in>set Ds. \<forall>z\<in>set D. edited_target L A Fs' z"
    and atoms: "fst ` set As\<subseteq>fst ` set As'"
    and kept: "\<And>F z. F\<in>set Fs \<Longrightarrow> z\<in>set F \<Longrightarrow> (\<exists>D\<in>set Ds. z\<in>set D) \<or> (\<exists>F'\<in>set Fs'. z\<in>set F')"
    and edge: "(p,k)\<in>reach_edges (state_reach_table As Rs Fs)"
    and lost: "(p,k)\<notin>reach_edges (state_reach_table As' Rs' Fs')"
  shows "k\<in>set L"
proof -
  obtain F z where Fz: "F\<in>set Fs" "z\<in>set F" "k\<in>set (row_mentions (snd z))" "p\<in>set (row_subjects (snd z))"
    and ka: "k\<in>fst ` set As"
    using edge by (auto simp: state_reach_table_edges)
  have none: "\<not>(\<exists>F'\<in>set Fs'. \<exists>z'\<in>set F'. k\<in>set (row_mentions (snd z')) \<and> p\<in>set (row_subjects (snd z')))"
    using lost ka atoms by (auto simp: state_reach_table_edges)
  obtain D where "D\<in>set Ds" "z\<in>set D" using kept[OF Fz(1,2)] none Fz(3,4) by blast
  then have "edited_target L A Fs' z" using targets by blast
  then show ?thesis using Fz(3,4) none unfolding edited_target_def by blast
qed

section \<open>The seeds, the seeded table and the restriction\<close>

definition one_key :: "state_key list \<Rightarrow> state_key list" where
  "one_key xs=(case remdups xs of [h] \<Rightarrow> [h] | _ \<Rightarrow> [])"

lemma one_key_member: "k\<in>set (one_key xs) \<longleftrightarrow> remdups xs=[k]"
  unfolding one_key_def by (auto split: list.split)

text \<open>
  The request state's reach roots: the keys that are the one key, declared or subject, of some row, and
  the keys the roots head. Each is read from the rows; none is a decision's answer.
\<close>

definition state_reach_seeds :: "state_rows \<Rightarrow> state_key list" where
  "state_reach_seeds R=concat (map (\<lambda>F. concat (map (\<lambda>z. one_key (row_declared (snd z)@row_subjects (snd z))) F))
    (state_all_families R))@state_root_keys (state_roots R)"

definition state_reach_roots :: "state_rows \<Rightarrow> reach_table" where
  "state_reach_roots R=map (\<lambda>k. (k,True,[])) (state_reach_seeds R)"

lemma state_reach_seeds_member:
  "k\<in>set (state_reach_seeds R) \<longleftrightarrow>
    (\<exists>F\<in>set (state_all_families R). \<exists>z\<in>set F. remdups (row_declared (snd z)@row_subjects (snd z))=[k]) \<or>
    k\<in>set (state_root_keys (state_roots R))"
  by (auto simp: state_reach_seeds_def one_key_member)

lemma state_reach_seeds_reached:
  assumes present: "state_presents key S R"
    and rows: "\<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) (state_all_families R))"
  shows "set (state_reach_seeds R)\<subseteq>table_reached (state_reach_table (state_atoms R) (state_roots R) (state_all_families R))"
proof
  fix k assume "k\<in>set (state_reach_seeds R)"
  then consider (row) F z where "F\<in>set (state_all_families R)" "z\<in>set F"
      "remdups (row_declared (snd z)@row_subjects (snd z))=[k]"
    | (root) "k\<in>set (state_root_keys (state_roots R))"
    by (auto simp: state_reach_seeds_member)
  then show "k\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) (state_all_families R))"
  proof cases
    case row
    have "set (remdups (row_declared (snd z)@row_subjects (snd z)))=set [k]" by (simp only: row(3))
    then have one: "set (row_declared (snd z))\<union>set (row_subjects (snd z))={k}"
      by (simp only: set_remdups set_append list.set)
    obtain h where "h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z))"
        "h\<in>table_reached (state_reach_table (state_atoms R) (state_roots R) (state_all_families R))"
      using bspec[OF bspec[OF rows row(1)] row(2)] by (elim bexE)
    with one show ?thesis by (simp only: singleton_iff)
  next
    case root
    then obtain q where q: "q\<in>set (map snd (state_roots R))" "k\<in>set (row_mentions q)"
      by (auto simp: state_root_keys_member)
    then obtain a where "(a,q)\<in>set (state_roots R)" by auto
    then have atom: "k\<in>fst ` set (state_atoms R)"
      using state_presents_root_cited_atoms[OF present] q(2) by blast
    have "(k,True,state_reach_predecessors (state_all_families R) k)\<in>set
        (state_reach_table (state_atoms R) (state_roots R) (state_all_families R))"
      using atom root by (simp add: state_reach_table_row)
    then show ?thesis by (rule table_reached.root)
  qed
qed

text \<open>Reach depends on the set of a table's rows, and a seeded table's edges are its own at unseeded keys.\<close>

lemma table_reached_set:
  assumes "set T=set U"
  shows "table_reached T=table_reached U"
  by (rule antisym; rule table_reached_mono) (simp_all add: assms)

lemma reach_edges_seeded: "reach_edges (reach_seeded K T)={(p,k). (p,k)\<in>reach_edges T \<and> k\<notin>K}"
  by (auto simp: reach_edges_member reach_seeded_member split: if_splits; blast)

text \<open>
  The seeded table \<open>T''\<close> is the reach roots at the seeds outside \<open>O\<close> and the answer table's row at every other
  key: \<open>O\<close>'s keys, the keys new to the answer table, and the keys no row speaks of. Its predecessors are the
  subjects of the answer state's mention fibre at the key (\<open>state_reach_predecessors\<close>).
\<close>

definition edited_reach_table :: "state_key list \<Rightarrow> state_key list \<Rightarrow> reach_table \<Rightarrow> reach_table" where
  "edited_reach_table K L T=reach_seeded (set K-set L) T"

lemma edited_reach_table_member:
  "(k,v)\<in>set (edited_reach_table K L T) \<longleftrightarrow>
    (\<exists>r ps. (k,r,ps)\<in>set T \<and> v=(if k\<in>set K-set L then (True,[]) else (r,ps)))"
  unfolding edited_reach_table_def by (rule reach_seeded_member)

section \<open>The field \<open>unreached\<close> on the edited state\<close>

text \<open>
  The rows checked: the added families, and the rows of the answer state at a key of \<open>O\<close>, about it or
  declaring it.
\<close>

definition edited_reach_families :: "state_edit \<Rightarrow> isabelle_context state_family list \<Rightarrow> state_key list \<Rightarrow>
    isabelle_context state_family list" where
  "edited_reach_families e Fs L=map (edit_added e) entity_kinds @
    concat (map (\<lambda>a. map (key_fibre row_subjects a) Fs @ map (key_fibre row_declared a) Fs) L)"

lemma edited_reach_families_member:
  "G\<in>set (edited_reach_families e Fs L) \<longleftrightarrow> (\<exists>j. G=edit_added e j) \<or>
    (\<exists>a\<in>set L. \<exists>F\<in>set Fs. G=key_fibre row_subjects a F \<or> G=key_fibre row_declared a F)"
  by (auto simp: edited_reach_families_def entity_kinds_all)

context edited_local
begin

abbreviation request_table :: reach_table where
  "request_table \<equiv> state_reach_table (state_atoms R) (state_roots R) (state_all_families R)"

abbreviation answer_table :: reach_table where
  "answer_table \<equiv> state_reach_table (state_atoms (edited_state R e)) (state_roots (edited_state R e))
    (state_all_families (edited_state R e))"

text \<open>
  The honest statement of the field: any checked families serve that are sound (every checked row a row of
  the answer state) and complete (the added rows, and every row of the answer state at a key of \<open>O\<close>, among
  them), and whose rows' keys the table can visit. Inclusions, never an equation, so a larger list, shared
  with another field's argument, costs work and never truth.
\<close>

theorem edited_unreached_rows:
  fixes C :: "isabelle_context state_family list"
  assumes closed: "isabelle_unreached_entities (fst S) (snd S)=[]"
    and closure: "\<forall>a\<in>set L. \<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L"
    and targets: "\<forall>D\<in>set (map (edit_removed e) entity_kinds). \<forall>z\<in>set D.
      edited_target L A (state_all_families (edited_state R e)) z"
    and seeds: "set K\<subseteq>set (state_reach_seeds R)"
    and formed: "reach_table_formed U"
    and table: "set U=set (reach_restricted (set V) (edited_reach_table K L answer_table))"
    and visit_closed: "\<And>p k. (p,k)\<in>reach_edges answer_table \<Longrightarrow> k\<in>set V \<Longrightarrow> k\<notin>set K-set L \<Longrightarrow> p\<in>set V"
    and sound: "\<And>G z. G\<in>set C \<Longrightarrow> z\<in>set G \<Longrightarrow> \<exists>F\<in>set (state_all_families (edited_state R e)). z\<in>set F"
    and added: "\<And>j z. z\<in>set (edit_added e j) \<Longrightarrow> \<exists>G\<in>set C. z\<in>set G"
    and fibred: "\<And>F z a. F\<in>set (state_all_families (edited_state R e)) \<Longrightarrow> z\<in>set F \<Longrightarrow> a\<in>set L \<Longrightarrow>
      a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z)) \<Longrightarrow> \<exists>G\<in>set C. z\<in>set G"
    and visit_rows: "\<forall>G\<in>set C. \<forall>z\<in>set G. set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V"
  shows "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (verdict_unreached,Pair_Term (reach_table_term answer_table) (state_families_term ident (state_all_families (edited_state R e))))
      \<in>positive_meaning verdict_unreached_system"
    and "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
proof -
  let ?R'="edited_state R e"
  let ?C="C"
  let ?T''="edited_reach_table K L answer_table"
  have closed_call: "(verdict_unreached,Pair_Term (reach_table_term request_table) (state_families_term ident
      (state_all_families R)))\<in>positive_meaning verdict_unreached_system"
    using native_unreached_exact[where ident=ident, OF request state_all_families_range identity] closed by simp
  have rowsT: "\<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached request_table"
    by (rule iffD1[OF native_unreached_rows[where ident=ident, OF state_reach_table_formed identity] closed_call])
  have atoms: "state_atoms ?R'=state_atoms R@edit_atoms e" by (simp add: edited_state_def)
  have roots: "reach_roots request_table\<subseteq>reach_roots answer_table"
    by (auto simp: state_reach_table_roots atoms)
  have kept: "\<And>F z. F\<in>set (state_all_families R) \<Longrightarrow> z\<in>set F \<Longrightarrow>
      (\<exists>D\<in>set (map (edit_removed e) entity_kinds). z\<in>set D) \<or> (\<exists>F'\<in>set (state_all_families ?R'). z\<in>set F')"
    by (auto simp: state_all_families_range edited_state_member entity_kinds_all)
  have tg: "\<And>p k. (p,k)\<in>reach_edges request_table \<Longrightarrow> (p,k)\<notin>reach_edges answer_table \<Longrightarrow> k\<in>set L"
    by (rule removal_targets_edges[OF targets _ kept]) (auto simp: atoms)
  have cl: "\<And>p k. (p,k)\<in>reach_edges request_table \<Longrightarrow> p\<in>set L \<Longrightarrow> k\<in>set L"
    by (rule removal_closure_edges[OF closure])
  have removal: "\<And>k. k\<in>table_reached request_table \<Longrightarrow> k\<notin>set L \<Longrightarrow> k\<in>table_reached answer_table"
    by (rule table_reached_removal[OF roots tg cl])
  have seeded: "set K-set L\<subseteq>table_reached answer_table"
    using seeds state_reach_seeds_reached[OF request rowsT] removal by blast
  have same: "table_reached ?T''=table_reached answer_table"
    unfolding edited_reach_table_def by (rule table_reached_seeded[OF seeded])
  have closedV: "\<And>p k. (p,k)\<in>reach_edges ?T'' \<Longrightarrow> k\<in>set V \<Longrightarrow> p\<in>set V"
    using visit_closed by (auto simp: edited_reach_table_def reach_edges_seeded)
  have reachedU: "table_reached U=table_reached (reach_restricted (set V) ?T'')"
    by (rule table_reached_set[OF table])
  have restr: "\<And>h. h\<in>set V \<Longrightarrow> h\<in>table_reached U \<longleftrightarrow> h\<in>table_reached answer_table"
    using table_reached_restricted[OF closedV] same reachedU by simp
  have below: "table_reached U\<subseteq>table_reached answer_table"
    using reachedU same table_reached_mono[of "reach_restricted (set V) ?T''" ?T''] by (auto simp: reach_restricted_def)
  have incr: "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident ?C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (\<forall>G\<in>set ?C. \<forall>z\<in>set G. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)). h\<in>table_reached U)"
    by (rule native_unreached_rows[where ident=ident, OF formed identity])
  have whole: "(verdict_unreached,Pair_Term (reach_table_term answer_table) (state_families_term ident
      (state_all_families ?R')))\<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (\<forall>F\<in>set (state_all_families ?R'). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached answer_table)"
    by (rule native_unreached_rows[where ident=ident, OF state_reach_table_formed identity])
  have eq: "(\<forall>G\<in>set ?C. \<forall>z\<in>set G. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached U) \<longleftrightarrow>
    (\<forall>F\<in>set (state_all_families ?R'). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached answer_table)"
  proof
    assume inc: "\<forall>G\<in>set ?C. \<forall>z\<in>set G. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached U"
    show "\<forall>F\<in>set (state_all_families ?R'). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached answer_table"
    proof (intro ballI)
      fix F z assume F: "F\<in>set (state_all_families ?R')" and z: "z\<in>set F"
      obtain j where Fj: "F=state_entities ?R' j" using F by (auto simp: state_all_families_range)
      show "\<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)). h\<in>table_reached answer_table"
      proof (cases "z\<in>set (edit_added e j)")
        case True
        have "\<exists>G\<in>set ?C. z\<in>set G" by (rule added[OF True])
        then show ?thesis using inc below by blast
      next
        case False
        then have zR: "z\<in>set (state_entities R j)" using z Fj edited_state_member by auto
        show ?thesis
        proof (cases "\<exists>a\<in>set L. a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z))")
          case True
          then obtain a where a: "a\<in>set L" "a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z))" by blast
          have "\<exists>G\<in>set ?C. z\<in>set G" by (rule fibred[OF F z a(1) a(2)])
          then show ?thesis using inc below by blast
        next
          case False
          have "state_entities R j\<in>set (state_all_families R)" by (simp add: state_all_families_range)
          then obtain h where h: "h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z))"
              "h\<in>table_reached request_table"
            using rowsT zR by blast
          then have "h\<notin>set L" using False by blast
          then show ?thesis using h removal by blast
        qed
      qed
    qed
  next
    assume wh: "\<forall>F\<in>set (state_all_families ?R'). \<forall>z\<in>set F. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)).
      h\<in>table_reached answer_table"
    show "\<forall>G\<in>set ?C. \<forall>z\<in>set G. \<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)). h\<in>table_reached U"
    proof (intro ballI)
      fix G z assume G: "G\<in>set ?C" and z: "z\<in>set G"
      have "\<exists>F\<in>set (state_all_families ?R'). z\<in>set F" by (rule sound[OF G z])
      then obtain h where h: "h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z))" "h\<in>table_reached answer_table"
        using wh by blast
      have "h\<in>set V" using visit_rows G z h(1) by blast
      then show "\<exists>h\<in>set (row_declared (snd z))\<union>set (row_subjects (snd z)). h\<in>table_reached U" using h restr by blast
    qed
  qed
  show first: "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident ?C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (verdict_unreached,Pair_Term (reach_table_term answer_table) (state_families_term ident (state_all_families ?R')))
      \<in>positive_meaning verdict_unreached_system"
    using incr whole eq by simp
  show "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident ?C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
    by (rule trans[OF first native_unreached_exact[where ident=ident, OF answer state_all_families_range identity]])
qed

text \<open>The field's own families: the added families and the fibres at the keys of \<open>O\<close>.\<close>

corollary edited_unreached:
  assumes closed: "isabelle_unreached_entities (fst S) (snd S)=[]"
    and closure: "\<forall>a\<in>set L. \<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L"
    and targets: "\<forall>D\<in>set (map (edit_removed e) entity_kinds). \<forall>z\<in>set D.
      edited_target L A (state_all_families (edited_state R e)) z"
    and seeds: "set K\<subseteq>set (state_reach_seeds R)"
    and formed: "reach_table_formed U"
    and table: "set U=set (reach_restricted (set V) (edited_reach_table K L answer_table))"
    and visit_closed: "\<And>p k. (p,k)\<in>reach_edges answer_table \<Longrightarrow> k\<in>set V \<Longrightarrow> k\<notin>set K-set L \<Longrightarrow> p\<in>set V"
    and visit_rows: "\<forall>G\<in>set (edited_reach_families e (state_all_families (edited_state R e)) L). \<forall>z\<in>set G.
      set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V"
  shows "(verdict_unreached,Pair_Term (reach_table_term U)
      (state_families_term ident (edited_reach_families e (state_all_families (edited_state R e)) L)))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow>
    (verdict_unreached,Pair_Term (reach_table_term answer_table) (state_families_term ident (state_all_families (edited_state R e))))
      \<in>positive_meaning verdict_unreached_system" (is ?whole)
    and "(verdict_unreached,Pair_Term (reach_table_term U)
      (state_families_term ident (edited_reach_families e (state_all_families (edited_state R e)) L)))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]" (is ?answer)
proof -
  let ?R'="edited_state R e"
  let ?C="edited_reach_families e (state_all_families ?R') L"
  have sound: "\<exists>F\<in>set (state_all_families ?R'). z\<in>set F" if G: "G\<in>set ?C" and z: "z\<in>set G" for G z
  proof -
    from G consider (add) j where "G=edit_added e j"
      | (fibre) a F where "F\<in>set (state_all_families ?R')"
        "G=key_fibre row_subjects a F \<or> G=key_fibre row_declared a F"
      by (auto simp: edited_reach_families_member)
    then show ?thesis
    proof cases
      case add
      then have "z\<in>set (state_entities ?R' j)" using z edited_state_member by blast
      then show ?thesis by (auto simp: state_all_families_range)
    next
      case fibre
      then show ?thesis using z by (auto simp: key_fibre_member)
    qed
  qed
  have added: "\<exists>G\<in>set ?C. z\<in>set G" if "z\<in>set (edit_added e j)" for j z
  proof -
    have "edit_added e j\<in>set ?C" by (auto simp: edited_reach_families_member)
    then show ?thesis using that by blast
  qed
  have fibred: "\<exists>G\<in>set ?C. z\<in>set G"
    if F: "F\<in>set (state_all_families ?R')" and z: "z\<in>set F" and a: "a\<in>set L"
      and k: "a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z))" for F z a
  proof -
    have "z\<in>set (key_fibre row_subjects a F) \<or> z\<in>set (key_fibre row_declared a F)"
      using k z by (auto simp: key_fibre_member)
    moreover have "key_fibre row_subjects a F\<in>set ?C" "key_fibre row_declared a F\<in>set ?C"
      using a F by (auto simp: edited_reach_families_member)
    ultimately show ?thesis by blast
  qed
  note general = edited_unreached_rows[OF closed closure targets seeds formed table visit_closed sound added
    fibred visit_rows]
  show ?whole by (rule general(1))
  show ?answer by (rule general(2))
qed

text \<open>The same judgment with \<open>O\<close> admitted natively: both readings are calls of the admission program.\<close>

corollary edited_unreached_admitted:
  assumes closed: "isabelle_unreached_entities (fst S) (snd S)=[]"
    and closure: "(removal_closure,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident L (state_all_families R)))
      (keys_term L))\<in>positive_meaning edited_reach_system"
    and targets: "(removal_targets,Pair_Term (Pair_Term (keys_term L)
      (subject_indexes_term ident A (state_all_families (edited_state R e))))
      (state_families_term ident (map (edit_removed e) entity_kinds)))\<in>positive_meaning edited_reach_system"
    and seeds: "set K\<subseteq>set (state_reach_seeds R)"
    and formed: "reach_table_formed U"
    and table: "set U=set (reach_restricted (set V) (edited_reach_table K L answer_table))"
    and visit_closed: "\<And>p k. (p,k)\<in>reach_edges answer_table \<Longrightarrow> k\<in>set V \<Longrightarrow> k\<notin>set K-set L \<Longrightarrow> p\<in>set V"
    and visit_rows: "\<forall>G\<in>set (edited_reach_families e (state_all_families (edited_state R e)) L). \<forall>z\<in>set G.
      set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V"
  shows "(verdict_unreached,Pair_Term (reach_table_term U)
      (state_families_term ident (edited_reach_families e (state_all_families (edited_state R e)) L)))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
proof -
  have c: "\<forall>a\<in>set L. \<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L"
    using closure native_closure_exact[where ident=ident, OF identity] by simp
  have t: "\<forall>D\<in>set (map (edit_removed e) entity_kinds). \<forall>z\<in>set D.
      edited_target L A (state_all_families (edited_state R e)) z"
    using targets native_targets_exact[where ident=ident, OF identity] by simp
  show ?thesis by (rule edited_unreached(2)[OF closed c t seeds formed table visit_closed visit_rows])
qed

text \<open>The same over any sound and complete checked families.\<close>

corollary edited_unreached_rows_admitted:
  fixes C :: "isabelle_context state_family list"
  assumes closed: "isabelle_unreached_entities (fst S) (snd S)=[]"
    and closure: "(removal_closure,Pair_Term (Pair_Term (keys_term L) (subject_indexes_term ident L (state_all_families R)))
      (keys_term L))\<in>positive_meaning edited_reach_system"
    and targets: "(removal_targets,Pair_Term (Pair_Term (keys_term L)
      (subject_indexes_term ident A (state_all_families (edited_state R e))))
      (state_families_term ident (map (edit_removed e) entity_kinds)))\<in>positive_meaning edited_reach_system"
    and seeds: "set K\<subseteq>set (state_reach_seeds R)"
    and formed: "reach_table_formed U"
    and table: "set U=set (reach_restricted (set V) (edited_reach_table K L answer_table))"
    and visit_closed: "\<And>p k. (p,k)\<in>reach_edges answer_table \<Longrightarrow> k\<in>set V \<Longrightarrow> k\<notin>set K-set L \<Longrightarrow> p\<in>set V"
    and sound: "\<And>G z. G\<in>set C \<Longrightarrow> z\<in>set G \<Longrightarrow> \<exists>F\<in>set (state_all_families (edited_state R e)). z\<in>set F"
    and added: "\<And>j z. z\<in>set (edit_added e j) \<Longrightarrow> \<exists>G\<in>set C. z\<in>set G"
    and fibred: "\<And>F z a. F\<in>set (state_all_families (edited_state R e)) \<Longrightarrow> z\<in>set F \<Longrightarrow> a\<in>set L \<Longrightarrow>
      a\<in>set (row_subjects (snd z)) \<or> a\<in>set (row_declared (snd z)) \<Longrightarrow> \<exists>G\<in>set C. z\<in>set G"
    and visit_rows: "\<forall>G\<in>set C. \<forall>z\<in>set G. set (row_declared (snd z))\<union>set (row_subjects (snd z))\<subseteq>set V"
  shows "(verdict_unreached,Pair_Term (reach_table_term U) (state_families_term ident C))
      \<in>positive_meaning verdict_unreached_system \<longleftrightarrow> isabelle_unreached_entities (fst S') (snd S')=[]"
proof -
  have c: "\<forall>a\<in>set L. \<forall>F\<in>set (state_all_families R). \<forall>z\<in>set F. a\<in>set (row_subjects (snd z)) \<longrightarrow>
      set (row_mentions (snd z))\<subseteq>set L"
    using closure native_closure_exact[where ident=ident, OF identity] by simp
  have t: "\<forall>D\<in>set (map (edit_removed e) entity_kinds). \<forall>z\<in>set D.
      edited_target L A (state_all_families (edited_state R e)) z"
    using targets native_targets_exact[where ident=ident, OF identity] by simp
  show ?thesis
    by (rule edited_unreached_rows(2)[OF closed c t seeds formed table visit_closed sound added fibred visit_rows])
qed

end

end
