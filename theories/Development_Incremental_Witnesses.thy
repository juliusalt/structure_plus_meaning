theory Development_Incremental_Witnesses
  imports Development_Incremental_Verdict Development_Verdict_Witnesses
begin

section \<open>The reasons a refusal carries, at the edit's parts\<close>

text \<open>
  Design 171's build 7. The incremental judgment (\<open>Development_Incremental_Verdict\<close>) reads each field
  of the verdict at the part an answer's edit gives; a refusal must also say which constants and rows
  offend, and those are the witnesses of task 44 (\<open>Development_Verdict_Witnesses\<close>). Each witness is
  called here at the same incremental part its field is called at, and each lemma states that the call
  there holds exactly when the call at the whole part on the answer state holds. No witness program is
  added and no field is redefined: the witnesses' own contracts are consumed by name, and the field
  lemmas of builds 3 and 4 by name where the witness meets its field.

  Under the premise \<open>P\<close> of the locale \<^locale>\<open>incremental_verdict\<close> (the request state closed) the request
  state's witnesses are empty, so the answer state's arise only among the rows the incremental parts
  visit: \<open>undeclared\<close>'s among the rows it checks and the roots mentioning a key a removed row declares,
  \<open>malformed\<close>'s among the added rows. \<open>excess\<close> reads the subject's fibres, which the edit's part gives
  exactly, so it needs no premise. The witnesses share the premise locale with the incremental parts:
  one set of premises, discharged once for the constructor, serves the fields and their reasons.

  Store absence is read only by the witnesses' own calls, in \<^const>\<open>verdict_witness_system\<close>; no
  field of the verdict's program reaches it, and acceptance reads none.
\<close>

context incremental_verdict
begin

section \<open>The witness of \<open>excess\<close>\<close>

text \<open>
  The witness is called at the index the field reads: the subject index restricted to the subject's key,
  over the subject's fibres from the request state's assessment and the edit. The support is the one list
  the field reads, presented as the store the witness searches for absence.
\<close>

lemma incremental_excess_witness:
  "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident (map fst (state_atoms (edited_state R e)))
        (map (state_entities (edited_state R e)) kr)))) (path_term d))
      \<in>positive_meaning verdict_witness_system"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S'))"
      and atom: "k\<in>set (map fst (state_atoms R))"
    using request_subject by blast
  have fibres: "assessment_fibres (state_assessment R) e k kr=edited_fibres R e k kr"
    by (rule assessment_fibres_edited[OF atom])
  have atom': "k\<in>set (map fst (state_atoms (edited_state R e)))"
    using atoms_present_atom[OF state_presents_atoms[OF answer] bound] kc by force
  have lhs: "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident [k] (edited_fibres R e k kr)))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<notin>set ks \<and> (\<exists>F\<in>set (edited_fibres R e k kr). \<exists>z\<in>set F.
      k\<in>set (row_subjects (snd z)) \<and> d\<in>set (row_mentions (snd z)))"
    by (rule native_excess_witness_rows[where ident=ident,OF identity]) simp
  have rhs: "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident (map fst (state_atoms (edited_state R e)))
        (map (state_entities (edited_state R e)) kr)))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<notin>set ks \<and> (\<exists>F\<in>set (map (state_entities (edited_state R e)) kr). \<exists>z\<in>set F.
      k\<in>set (row_subjects (snd z)) \<and> d\<in>set (row_mentions (snd z)))"
    by (rule native_excess_witness_rows[where ident=ident,OF identity atom'])
  have some: "(\<exists>F\<in>set (edited_fibres R e k kr). \<exists>z\<in>set F.
      k\<in>set (row_subjects (snd z)) \<and> d\<in>set (row_mentions (snd z))) \<longleftrightarrow>
    (\<exists>F\<in>set (map (state_entities (edited_state R e)) kr). \<exists>z\<in>set F.
      k\<in>set (row_subjects (snd z)) \<and> d\<in>set (row_mentions (snd z)))"
    unfolding edited_fibres_whole by (simp add: key_fibre_def Bex_def; blast)
  show ?thesis unfolding fibres lhs rhs some ..
qed

text \<open>At a key of the answer state, the witness at the incremental part states exactly the members of the
  verdict's own list, \<^const>\<open>development_answer_statements_excess\<close>, which the repair reads.\<close>

lemma incremental_excess_witness_exact:
  assumes kc: "k=key c" and bound: "c<length (fst (snd S'))" and dbound: "d<length (fst (snd S'))"
    and support: "\<And>x. x<length (fst (snd S')) \<Longrightarrow> key x\<in>set ks \<longleftrightarrow> x |\<in>| Y"
  shows "(witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))) (path_term (key d)))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    d\<in>set (development_answer_statements_excess replaceable (snd S') {|c|} Y)"
proof -
  have selection: "set (map (state_entities (edited_state R e)) kr)=state_entities (edited_state R e) ` set kr"
    by simp
  show ?thesis
    unfolding incremental_excess_witness unfolding kc
    by (rule native_excess_witness_exact[where ident=ident,OF answer replaceable_kinds selection bound dbound
      support identity])
qed

text \<open>
  The field and its reasons from the same local calls: the field \<open>excess\<close> at its incremental part holds
  exactly when no key of the answer state is a witness at the same part. The field's side is build 3's
  contract (@{thm [source] edited_excess}), the equivalence at the whole part task 44's
  (@{thm [source] native_excess_no_witness}), and the witness moves to its incremental part by the first
  lemma above; none is proved again, and neither side is the other's negation.
\<close>

corollary incremental_excess_reasons:
  "(verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks))
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow>
    (\<forall>d<length (fst (snd S')). (witness_excess,Pair_Term (Pair_Term (path_term k) (Pair_Term (support_term ks)
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))) (path_term (key d)))
      \<notin>positive_meaning verdict_witness_system)"
proof -
  obtain c where kc: "k=key c" and bound: "c<length (fst (snd S'))"
      and atom: "k\<in>set (map fst (state_atoms R))"
    using request_subject by blast
  let ?Y="fset_of_list (filter (\<lambda>d. key d\<in>set ks) [0..<length (fst (snd S'))])"
  let ?L="development_answer_statements_excess replaceable (snd S') {|c|} ?Y"
  have support: "key d\<in>set ks \<longleftrightarrow> d |\<in>| ?Y" if "d<length (fst (snd S'))" for d
    using that by (simp add: fset_of_list_elem)
  have fibres: "assessment_fibres (state_assessment R) e k kr=edited_fibres R e k kr"
    by (rule assessment_fibres_edited[OF atom])
  have field: "(verdict_excess,Pair_Term (Pair_Term (path_term k) (keys_term ks))
      (subject_indexes_term ident [k] (assessment_fibres (state_assessment R) e k kr)))
      \<in>positive_meaning native_verdict_system \<longleftrightarrow> ?L=[]"
    unfolding fibres using edited_excess(2)[OF replaceable_kinds bound support] by (simp add: excess_here kc)
  have selection: "set (map (state_entities (edited_state R e)) kr)=state_entities (edited_state R e) ` set kr"
    by simp
  have inside: "d<length (fst (snd S'))" if member: "d\<in>set ?L" for d
  proof -
    obtain g where g: "g\<in>set (development_answer_statements replaceable (snd S') {|c|})"
        and m: "d\<in>set (entity_mentions g)"
      using member answer_statements_excess_member[of d replaceable "snd S'" "{|c|}" ?Y] by blast
    have "g\<in>set (snd (snd S'))" using g by (simp add: development_answer_statements_def)
    then show ?thesis using m by (rule state_presents_mentions_inside[OF answer])
  qed
  show ?thesis
    unfolding field incremental_excess_witness unfolding kc
    by (rule native_excess_no_witness[where ident=ident,OF answer replaceable_kinds selection bound support
      identity inside])
qed

section \<open>The witness of \<open>undeclared\<close>\<close>

text \<open>
  The witness is called at the part the field is called at in @{thm [source] incremental_undeclared}: the
  families it checks, the roots mentioning a key a removed row declares, and the answer state's
  declaration store restricted to the keys those rows and roots mention. At a key those rows or roots
  mention the restricted store has the whole store's presence (@{thm [source] edited_undeclared_keys_store}),
  so absence there is absence in the answer state. Conversely a key undeclared in the answer state and
  mentioned by one of its rows or roots is mentioned by a checked one: build 4's pointwise host argument
  (@{thm [source] edited_mentions_checked}), whose premises are the discharges both judgments consume, stated
  once in the locale (\<open>undeclared_request_closed\<close>, \<open>undeclared_edited_rows\<close>,
  \<open>undeclared_checked_families\<close>, \<open>undeclared_checked_roots\<close>).

  The closedness is read through the field's contracts (@{thm [source] native_undeclared_exact},
  @{thm [source] native_mentions_found}); the witness's through its own
  (@{thm [source] undeclared_witness_at}, the store absence and the \<open>some\<close>-readings of task 44).
\<close>

lemma incremental_undeclared_witness:
  fixes L :: "state_key list" and d :: state_key
  defines "X\<equiv>assessment_families_checked (state_assessment R) e L (edit_removed_declarations e)"
    and "Rc\<equiv>edited_undeclared_roots (state_roots R) (edit_removed_declarations e)"
  assumes L_atoms: "set L\<subseteq>set (map fst (state_atoms R))"
    and ms_atoms: "set (edit_removed_declarations e)\<subseteq>set (map fst (state_atoms R))"
    and single: "declarations_single_valued (state_all_families R)"
  shows "(witness_undeclared,Pair_Term (Pair_Term (restricted_declaration_term (edited_undeclared_keys X Rc)
        (state_all_families (edited_state R e)))
      (Pair_Term (state_families_term ident X) (state_family_term identr Rc))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (witness_undeclared,Pair_Term (Pair_Term (declaration_term (state_all_families (edited_state R e)))
      (Pair_Term (state_families_term ident (state_all_families (edited_state R e)))
        (state_family_term identr (state_roots (edited_state R e))))) (path_term d))
      \<in>positive_meaning verdict_witness_system"
proof -
  let ?Fs'="state_all_families (edited_state R e)"
  let ?Fs="state_all_families R"
  let ?ms="edit_removed_declarations e"
  let ?T="path_store (filter (\<lambda>r. fst r\<in>set (edited_undeclared_keys X Rc)) (declaration_rows ?Fs'))"
  interpret families: selection_some_reading verdict_witness_system witness_selection_some
      witness_family_some witness_row_mentions path_term ident "\<lambda>d z. d\<in>set (row_mentions (snd z))"
    by unfold_locales (simp_all add: identity witness_mentioned_rows[where ident=ident,OF identity])
  interpret rootrows: family_some_reading verdict_witness_system witness_family_some
      witness_row_mentions path_term identr "\<lambda>d z. d\<in>set (row_mentions (snd z))"
    by unfold_locales (simp_all add: roots_identity witness_mentioned_rows[where ident=identr,OF roots_identity])
  have fam: "\<And>F. term_formed (state_family_term ident F)" by (rule state_family_term_formed) (rule identity)
  have ffs: "term_formed (state_families_term ident Fs)" for Fs
    unfolding state_families_term_def by (induction Fs) (simp_all add: fam octets_formed_def)
  have frs: "term_formed (state_family_term identr Rs)" for Rs
    by (rule state_family_term_formed) (rule roots_identity)
  have abs_inc: "(witness_absent,Pair_Term (path_term d) (Pair_Term (path_term d)
      (restricted_declaration_term (edited_undeclared_keys X Rc) ?Fs')))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> store_lookup ?T d=None"
    using witness_absences.exact_at_path[of path_term "path_term d" d ?T]
    by (simp add: restricted_declaration_term_def)
  have abs_whole: "(witness_absent,Pair_Term (path_term d) (Pair_Term (path_term d) (declaration_term ?Fs')))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow> store_lookup (declaration_store ?Fs') d=None"
    using witness_absences.exact_at_path[of path_term "path_term d" d "declaration_store ?Fs'"]
    by (simp add: declaration_term_def)
  have inc: "(witness_undeclared,Pair_Term (Pair_Term (restricted_declaration_term (edited_undeclared_keys X Rc) ?Fs')
      (Pair_Term (state_families_term ident X) (state_family_term identr Rc))) (path_term d))
      \<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    store_lookup ?T d=None \<and> ((\<exists>G\<in>set X. \<exists>z\<in>set G. d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set Rc. d\<in>set (row_mentions (snd z))))"
    by (simp only: undeclared_witness_at[OF ffs frs] abs_inc families.exact rootrows.exact path_term_formed
      simp_thms)
  have whole: "(witness_undeclared,Pair_Term (Pair_Term (declaration_term ?Fs')
      (Pair_Term (state_families_term ident ?Fs') (state_family_term identr (state_roots (edited_state R e)))))
      (path_term d))\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    store_lookup (declaration_store ?Fs') d=None \<and> ((\<exists>F\<in>set ?Fs'. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set (state_roots R). d\<in>set (row_mentions (snd z))))"
    by (simp only: undeclared_witness_at[OF ffs frs] abs_whole families.exact rootrows.exact path_term_formed
      simp_thms edited_state_roots)
  note closed = undeclared_request_closed
  have closed_mentions: "(\<forall>F\<in>set ?Fs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)).
      store_lookup (declaration_store ?Fs) q\<noteq>None) \<and>
    (\<forall>z\<in>set (state_roots R). \<forall>q\<in>set (row_mentions (snd z)). store_lookup (declaration_store ?Fs) q\<noteq>None)"
    by (rule iffD1[OF native_mentions_found[where val=path_term and T="declaration_store ?Fs" and Fs="?Fs"
      and Rs="state_roots R",OF identity roots_identity path_term_formed] closed[unfolded declaration_term_def]])
  note rows = undeclared_edited_rows
  note sound = undeclared_checked_sound[OF L_atoms ms_atoms single, folded X_def]
    and added = undeclared_checked_added[OF L_atoms ms_atoms single, folded X_def]
    and mentioning = undeclared_checked_mentioning[OF L_atoms ms_atoms single, folded X_def]
    and croots = undeclared_checked_roots[folded Rc_def]
  have declared: "\<exists>F\<in>set ?Fs. \<exists>w\<in>set F. q\<in>set (row_declared (snd w))"
    if "store_lookup (declaration_store ?Fs) q\<noteq>None" for q
    using that declaration_store_declared[of ?Fs q] by blast
  have declared': "store_lookup (declaration_store ?Fs') q\<noteq>None \<longleftrightarrow>
      (\<exists>F\<in>set ?Fs'. \<exists>w\<in>set F. q\<in>set (row_declared (snd w)))" for q
    using declaration_store_declared[of ?Fs' q] by blast
  note keys = edit_removed_declared
  note checked = edited_mentions_checked[where decl="\<lambda>q. store_lookup (declaration_store ?Fs) q\<noteq>None"
    and decl'="\<lambda>q. store_lookup (declaration_store ?Fs') q\<noteq>None",
    OF closed_mentions[THEN conjunct1] closed_mentions[THEN conjunct2] declared declared' rows keys added
    mentioning croots]
  show ?thesis
    unfolding inc whole
  proof
    assume given: "store_lookup ?T d=None \<and> ((\<exists>G\<in>set X. \<exists>z\<in>set G. d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set Rc. d\<in>set (row_mentions (snd z))))"
    then have none: "store_lookup ?T d=None" by blast
    from given have "(\<exists>G\<in>set X. \<exists>z\<in>set G. d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set Rc. d\<in>set (row_mentions (snd z)))" by blast
    then show "store_lookup (declaration_store ?Fs') d=None \<and>
      ((\<exists>F\<in>set ?Fs'. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))) \<or>
       (\<exists>z\<in>set (state_roots R). d\<in>set (row_mentions (snd z))))"
    proof
      assume "\<exists>G\<in>set X. \<exists>z\<in>set G. d\<in>set (row_mentions (snd z))"
      then obtain G z where G: "G\<in>set X" "z\<in>set G" "d\<in>set (row_mentions (snd z))" by blast
      have zin: "z\<in>(\<Union>G\<in>set X. set G)" using G by blast
      have same: "store_lookup ?T d\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') d\<noteq>None"
        by (rule edited_undeclared_keys_store[OF zin G(3)])
      obtain F where "F\<in>set ?Fs'" "z\<in>set F" using sound[OF zin] by blast
      then show ?thesis using none same G(3) by blast
    next
      assume "\<exists>z\<in>set Rc. d\<in>set (row_mentions (snd z))"
      then obtain z where z: "z\<in>set Rc" "d\<in>set (row_mentions (snd z))" by blast
      have same: "store_lookup ?T d\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') d\<noteq>None"
        by (rule edited_undeclared_keys_store_roots[OF z])
      have "z\<in>set (state_roots R)" using z(1) unfolding Rc_def edited_undeclared_roots_member by blast
      then show ?thesis using none same z(2) by blast
    qed
  next
    assume given: "store_lookup (declaration_store ?Fs') d=None \<and>
      ((\<exists>F\<in>set ?Fs'. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))) \<or>
       (\<exists>z\<in>set (state_roots R). d\<in>set (row_mentions (snd z))))"
    then have none: "store_lookup (declaration_store ?Fs') d=None" by blast
    have undecl: "\<not>store_lookup (declaration_store ?Fs') d\<noteq>None" using none by simp
    from given have "(\<exists>F\<in>set ?Fs'. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))) \<or>
       (\<exists>z\<in>set (state_roots R). d\<in>set (row_mentions (snd z)))" by blast
    then show "store_lookup ?T d=None \<and> ((\<exists>G\<in>set X. \<exists>z\<in>set G. d\<in>set (row_mentions (snd z))) \<or>
      (\<exists>z\<in>set Rc. d\<in>set (row_mentions (snd z))))"
    proof
      assume "\<exists>F\<in>set ?Fs'. \<exists>z\<in>set F. d\<in>set (row_mentions (snd z))"
      then obtain F z where F: "F\<in>set ?Fs'" "z\<in>set F" "d\<in>set (row_mentions (snd z))" by blast
      have zin: "z\<in>(\<Union>F\<in>set ?Fs'. set F)" using F(1,2) by (rule UN_I)
      have zX: "z\<in>(\<Union>G\<in>set X. set G)" by (rule checked(1)) (assumption | fact undecl zin F(3))+
      have same: "store_lookup ?T d\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') d\<noteq>None"
        by (rule edited_undeclared_keys_store[OF zX F(3)])
      show ?thesis using zX F(3) none same by blast
    next
      assume "\<exists>z\<in>set (state_roots R). d\<in>set (row_mentions (snd z))"
      then obtain z where z: "z\<in>set (state_roots R)" "d\<in>set (row_mentions (snd z))" by blast
      have zR: "z\<in>set Rc" by (rule checked(2)) (assumption | fact undecl z(1) z(2))+
      have same: "store_lookup ?T d\<noteq>None \<longleftrightarrow> store_lookup (declaration_store ?Fs') d\<noteq>None"
        by (rule edited_undeclared_keys_store_roots[OF zR z(2)])
      show ?thesis using zR z(2) none same by blast
    qed
  qed
qed

section \<open>The witness of \<open>malformed\<close>\<close>

text \<open>
  The witness is a relation of rows, called at the rows its field reads: at its incremental part, the
  rows of the added families outside the specifications (@{thm [source] incremental_formed}). A row of
  the answer state outside those is a row of the request state, whose malformed entities are none
  (@{thm [source] native_malformed_witness_exact}), so the witness holds of it nowhere: the rows the
  witness holds of among the added rows are all it holds of among the answer state's.
\<close>

lemma incremental_malformed_witness:
  "(\<exists>F\<in>set (map (edit_added e) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system \<longleftrightarrow>
    (\<exists>F\<in>set (map (state_entities (edited_state R e)) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
proof
  assume "(\<exists>F\<in>set (map (edit_added e) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
  then show "(\<exists>F\<in>set (map (state_entities (edited_state R e)) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
    by (auto simp: edited_state_member)
next
  assume given: "(\<exists>F\<in>set (map (state_entities (edited_state R e)) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
  then obtain j where j: "j\<noteq>Specification_Kind" and z: "z\<in>set (state_entities (edited_state R e) j)" by auto
  have w: "(witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
    using given by blast
  show "(\<exists>F\<in>set (map (edit_added e) (kinds_outside [Specification_Kind])). z\<in>set F) \<and>
      (witness_malformed,Pair_Term x (state_row_term ident z))\<in>positive_meaning verdict_witness_system"
  proof (cases "z\<in>set (edit_added e j)")
    case True
    then show ?thesis using j w by auto
  next
    case False
    then have old: "z\<in>set (state_entities R j)" using z edited_state_member by blast
    obtain a p where zp: "z=(a,p)" by (cases z)
    obtain g where g: "g\<in>set (snd (snd S))" "entity_kind_of g=j" "p=entity_row key (snd S) g"
      using state_presents_row_origin[OF request old[unfolded zp]] by auto
    have xf: "term_formed x"
      using iffD1[OF native_malformed_witness_row[where ident=ident,OF identity] w] by blast
    have "g\<in>set (isabelle_malformed_entities (snd S))"
      using native_malformed_witness_exact[where ident=ident and key=key and a=a,OF identity xf g(1)] w zp g(2,3) j
      by simp
    then show ?thesis using closed_malformed by simp
  qed
qed

end

end
