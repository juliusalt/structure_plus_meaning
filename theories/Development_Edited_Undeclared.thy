theory Development_Edited_Undeclared
  imports Development_State_Edit
begin

section \<open>The field \<open>undeclared\<close> of an answer state, read from its request state and the edit\<close>

text \<open>
  On an answer state, \<open>undeclared\<close> need not read every row (design 171, "Each field on the edited state").
  Its request state is closed, so every mention of a kept row was declared there. A kept mention stays
  declared unless its declaring row is removed; then the row mentions a key that a removed row declares.
  So the rows checked are the added families, the rows of the answer state mentioning a key that a removed
  row declares, and the roots mentioning such a key; the last two are the fibres of the mention index at
  those keys (\<open>key_index_lookup\<close> finds exactly them at an atom of the state). They are checked against the
  answer state's declaration store restricted to the keys they mention (\<open>path_store_restrict\<close>), which
  reads the same presence at each of those keys. No program is added: the call is the field's own
  (\<open>verdict_undeclared\<close>) at other arguments, and its contract \<open>native_mentions_found\<close> is consumed at both.
  Presence alone is read: the declaration store's single-valuedness is not needed and no absence enters.
  A key list larger than the removed declarations costs work, never truth.
\<close>

definition edited_undeclared_families ::
    "'i state_family list \<Rightarrow> 'i state_family list \<Rightarrow> state_key list \<Rightarrow> 'i state_family list" where
  "edited_undeclared_families As Fs ks=As @ concat (map (\<lambda>a. map (mention_fibre a) Fs) ks)"

definition edited_undeclared_roots :: "'j state_family \<Rightarrow> state_key list \<Rightarrow> 'j state_family" where
  "edited_undeclared_roots Rs ks=concat (map (\<lambda>a. mention_fibre a Rs) ks)"

definition edited_undeclared_keys :: "'i state_family list \<Rightarrow> 'j state_family \<Rightarrow> state_key list" where
  "edited_undeclared_keys Gs Rc=concat (map (\<lambda>z. row_mentions (snd z)) (concat Gs)) @
    concat (map (\<lambda>z. row_mentions (snd z)) Rc)"

definition restricted_declaration_term :: "state_key list \<Rightarrow> 'i state_family list \<Rightarrow> factor_term" where
  "restricted_declaration_term ms Fs=store_term path_term (path_store (filter (\<lambda>r. fst r\<in>set ms) (declaration_rows Fs)))"

section \<open>The rows checked suffice on a closed request state\<close>

text \<open>
  The host argument, over any declaration readings: the request state's mentions are declared, the answer
  state's rows are the kept rows followed by the added ones, and a removed row declares only keys of the list.
  Then the checked rows' mentions are declared in the answer state exactly when all its rows' and roots' are.
\<close>

lemma edited_mentions_closed:
  fixes Fs Fs' As Gs :: "'i state_family list" and Rs Rc :: "'j state_family"
    and D :: "(state_key\<times>'i state_row) set" and decl decl' dr :: "state_key \<Rightarrow> bool"
  assumes closed: "\<forall>F\<in>set Fs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). decl q"
    and closed_roots: "\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). decl q"
    and declared: "\<And>q. decl q \<Longrightarrow> \<exists>F\<in>set Fs. \<exists>w\<in>set F. q\<in>set (row_declared (snd w))"
    and declared': "\<And>q. decl' q \<longleftrightarrow> (\<exists>F\<in>set Fs'. \<exists>w\<in>set F. q\<in>set (row_declared (snd w)))"
    and rows: "(\<Union>F\<in>set Fs'. set F)=(\<Union>F\<in>set Fs. set F)-D \<union> (\<Union>F\<in>set As. set F)"
    and keys: "\<And>z d. z\<in>D \<Longrightarrow> d\<in>set (row_declared (snd z)) \<Longrightarrow> d\<in>set ks"
    and checked: "\<And>z. z\<in>(\<Union>F\<in>set Gs. set F) \<longleftrightarrow>
      z\<in>(\<Union>F\<in>set As. set F) \<or> (z\<in>(\<Union>F\<in>set Fs'. set F) \<and> (\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z))))"
    and checked_roots: "\<And>z. z\<in>set Rc \<longleftrightarrow> z\<in>set Rs \<and> (\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z)))"
    and restricted: "\<And>z q. z\<in>(\<Union>F\<in>set Gs. set F) \<Longrightarrow> q\<in>set (row_mentions (snd z)) \<Longrightarrow>
      dr q \<longleftrightarrow> decl' q"
    and restricted_roots: "\<And>z q. z\<in>set Rc \<Longrightarrow> q\<in>set (row_mentions (snd z)) \<Longrightarrow> dr q \<longleftrightarrow> decl' q"
  shows "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). dr q) \<and>
      (\<forall>z\<in>set Rc. \<forall>q\<in>set (row_mentions (snd z)). dr q) \<longleftrightarrow>
    (\<forall>F\<in>set Fs'. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). decl' q) \<and>
      (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). decl' q)"
proof -
  have mem: "z\<in>(\<Union>F\<in>set Fs'. set F) \<longleftrightarrow> (z\<in>(\<Union>F\<in>set Fs. set F) \<and> z\<notin>D) \<or> z\<in>(\<Union>F\<in>set As. set F)" for z
    by (simp only: rows Un_iff Diff_iff)
  show ?thesis
  proof
  assume inc: "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). dr q) \<and>
      (\<forall>z\<in>set Rc. \<forall>q\<in>set (row_mentions (snd z)). dr q)"
  have rows_checked: "decl' q" if z: "z\<in>(\<Union>F\<in>set Gs. set F)" and q: "q\<in>set (row_mentions (snd z))" for z q
  proof -
    obtain F where F: "F\<in>set Gs" "z\<in>set F" using z by blast
    have "dr q" using inc F q by blast
    then show ?thesis using restricted[OF z q] by blast
  qed
  have roots_checked: "decl' q" if z: "z\<in>set Rc" and q: "q\<in>set (row_mentions (snd z))" for z q
  proof -
    have "dr q" using inc z q by blast
    then show ?thesis using restricted_roots[OF z q] by blast
  qed
  have kept_or_removed: "decl' q \<or> q\<in>set ks" if d: "decl q" for q
  proof -
    obtain F w where F: "F\<in>set Fs" "w\<in>set F" "q\<in>set (row_declared (snd w))" using declared[OF d] by blast
    show ?thesis
    proof (cases "w\<in>D")
      case True
      then show ?thesis using keys[OF True F(3)] by blast
    next
      case False
      have "w\<in>(\<Union>F\<in>set Fs'. set F)"
        using mem[of w] UN_I[where B=set, OF F(1) F(2)] False by (simp only: simp_thms)
      then have "decl' q" unfolding declared' using F(3) by blast
      then show ?thesis by (rule disjI1)
    qed
  qed
  have rows_all: "\<forall>F\<in>set Fs'. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). decl' q"
  proof (intro ballI)
    fix F z q
    assume F: "F\<in>set Fs'" and z: "z\<in>set F" and q: "q\<in>set (row_mentions (snd z))"
    have zR': "z\<in>(\<Union>F\<in>set Fs'. set F)" by (rule UN_I[where B=set, OF F z])
    show "decl' q"
    proof (cases "z\<in>(\<Union>F\<in>set As. set F)")
      case True
      then have "z\<in>(\<Union>F\<in>set Gs. set F)" using checked[of z] by (simp only: simp_thms)
      then show ?thesis using rows_checked q by blast
    next
      case False
      then have "z\<in>(\<Union>F\<in>set Fs. set F)" using zR' mem[of z] by (simp only: simp_thms)
      then obtain G where "G\<in>set Fs" "z\<in>set G" by (rule UN_E)
      then have "decl q" using closed q by blast
      then consider "decl' q" | "q\<in>set ks" using kept_or_removed by blast
      then show ?thesis
      proof cases
        case 2
        then have "\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z))" using q by (rule bexI[rotated])
        then have "z\<in>(\<Union>F\<in>set Gs. set F)" using checked[of z] zR' by (simp only: simp_thms)
        then show ?thesis using rows_checked q by blast
      qed
    qed
  qed
  have roots_all: "\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). decl' q"
  proof (intro ballI)
    fix z q
    assume z: "z\<in>set Rs" and q: "q\<in>set (row_mentions (snd z))"
    have "decl q" using closed_roots z q by blast
    then consider "decl' q" | "q\<in>set ks" using kept_or_removed by blast
    then show "decl' q"
    proof cases
      case 2
      then have "\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z))" using q by (rule bexI[rotated])
      then have "z\<in>set Rc" using checked_roots[of z] z by (simp only: simp_thms)
      then show ?thesis using roots_checked q by blast
    qed
  qed
  show "(\<forall>F\<in>set Fs'. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). decl' q) \<and>
      (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). decl' q)"
    using rows_all roots_all by (rule conjI)
next
  assume whole: "(\<forall>F\<in>set Fs'. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). decl' q) \<and>
      (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). decl' q)"
  show "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). dr q) \<and>
      (\<forall>z\<in>set Rc. \<forall>q\<in>set (row_mentions (snd z)). dr q)"
  proof (intro conjI ballI)
    fix F z q
    assume F: "F\<in>set Gs" and z: "z\<in>set F" and q: "q\<in>set (row_mentions (snd z))"
    have zG: "z\<in>(\<Union>F\<in>set Gs. set F)" by (rule UN_I[where B=set, OF F z])
    have "z\<in>(\<Union>F\<in>set As. set F) \<or> z\<in>(\<Union>F\<in>set Fs'. set F)" using checked[of z] zG by (simp only: simp_thms) blast
    then have "z\<in>(\<Union>F\<in>set Fs'. set F)" using mem[of z] by (simp only: simp_thms) blast
    then obtain G where "G\<in>set Fs'" "z\<in>set G" by (rule UN_E)
    then have "decl' q" using whole q by blast
    then show "dr q" using restricted[OF zG q] by blast
  next
    fix z q
    assume z: "z\<in>set Rc" and q: "q\<in>set (row_mentions (snd z))"
    have "z\<in>set Rs" using checked_roots[of z] z by blast
    then have "decl' q" using whole q by blast
    then show "dr q" using restricted_roots[OF z q] by blast
  qed
  qed
qed

section \<open>The call at its incremental part is the call at its whole part\<close>

theorem edited_undeclared:
  fixes Fs Fs' As :: "'i state_family list" and Rs :: "'j state_family" and D :: "(state_key\<times>'i state_row) set"
    and ks :: "state_key list"
  defines "Gs\<equiv>edited_undeclared_families As Fs' ks" and "Rc\<equiv>edited_undeclared_roots Rs ks"
  assumes identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
    and closed: "(verdict_undeclared,Pair_Term (declaration_term Fs) (Pair_Term (state_families_term ident Fs)
      (state_family_term identr Rs)))\<in>positive_meaning verdict_mentions_system"
    and rows: "(\<Union>F\<in>set Fs'. set F)=(\<Union>F\<in>set Fs. set F)-D \<union> (\<Union>F\<in>set As. set F)"
    and keys: "\<And>z d. z\<in>D \<Longrightarrow> d\<in>set (row_declared (snd z)) \<Longrightarrow> d\<in>set ks"
  shows "(verdict_undeclared,Pair_Term (restricted_declaration_term (edited_undeclared_keys Gs Rc) Fs')
      (Pair_Term (state_families_term ident Gs) (state_family_term identr Rc)))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    (verdict_undeclared,Pair_Term (declaration_term Fs') (Pair_Term (state_families_term ident Fs')
      (state_family_term identr Rs)))\<in>positive_meaning verdict_mentions_system"
proof -
  let ?ms="edited_undeclared_keys Gs Rc"
  have pv: "\<And>y. term_formed (path_term y)" by simp
  note found = native_mentions_found[OF identity roots pv]
  have cl: "(\<forall>F\<in>set Fs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). store_lookup (declaration_store Fs) q\<noteq>None) \<and>
      (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). store_lookup (declaration_store Fs) q\<noteq>None)"
    using closed[unfolded declaration_term_def found] .
  have declared: "\<exists>F\<in>set Fs. \<exists>w\<in>set F. q\<in>set (row_declared (snd w))"
    if "store_lookup (declaration_store Fs) q\<noteq>None" for q
    using that unfolding declaration_store_declared .
  have declared': "store_lookup (declaration_store Fs') q\<noteq>None \<longleftrightarrow>
      (\<exists>F\<in>set Fs'. \<exists>w\<in>set F. q\<in>set (row_declared (snd w)))" for q
    by (rule declaration_store_declared)
  have checked: "z\<in>(\<Union>F\<in>set Gs. set F) \<longleftrightarrow> z\<in>(\<Union>F\<in>set As. set F) \<or>
      (z\<in>(\<Union>F\<in>set Fs'. set F) \<and> (\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z))))" for z
    unfolding Gs_def edited_undeclared_families_def by (auto simp: key_fibre_member)
  have checked_roots: "z\<in>set Rc \<longleftrightarrow> z\<in>set Rs \<and> (\<exists>a\<in>set ks. a\<in>set (row_mentions (snd z)))" for z
    unfolding Rc_def edited_undeclared_roots_def by (auto simp: key_fibre_member)
  have restricted: "store_lookup (path_store (filter (\<lambda>r. fst r\<in>set ?ms) (declaration_rows Fs'))) q\<noteq>None \<longleftrightarrow>
      store_lookup (declaration_store Fs') q\<noteq>None"
    if z: "z\<in>(\<Union>F\<in>set Gs. set F)" and q: "q\<in>set (row_mentions (snd z))" for z q
  proof -
    have "q\<in>set ?ms" using z q by (auto simp: edited_undeclared_keys_def)
    then show ?thesis by (simp add: path_store_restrict declaration_store_def)
  qed
  have restricted_roots: "store_lookup (path_store (filter (\<lambda>r. fst r\<in>set ?ms) (declaration_rows Fs'))) q\<noteq>None \<longleftrightarrow>
      store_lookup (declaration_store Fs') q\<noteq>None"
    if z: "z\<in>set Rc" and q: "q\<in>set (row_mentions (snd z))" for z q
  proof -
    have "q\<in>set ?ms" using z q by (auto simp: edited_undeclared_keys_def)
    then show ?thesis by (simp add: path_store_restrict declaration_store_def)
  qed
  have "(\<forall>F\<in>set Gs. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)).
        store_lookup (path_store (filter (\<lambda>r. fst r\<in>set ?ms) (declaration_rows Fs'))) q\<noteq>None) \<and>
      (\<forall>z\<in>set Rc. \<forall>q\<in>set (row_mentions (snd z)).
        store_lookup (path_store (filter (\<lambda>r. fst r\<in>set ?ms) (declaration_rows Fs'))) q\<noteq>None) \<longleftrightarrow>
    (\<forall>F\<in>set Fs'. \<forall>z\<in>set F. \<forall>q\<in>set (row_mentions (snd z)). store_lookup (declaration_store Fs') q\<noteq>None) \<and>
      (\<forall>z\<in>set Rs. \<forall>q\<in>set (row_mentions (snd z)). store_lookup (declaration_store Fs') q\<noteq>None)"
    by (rule edited_mentions_closed[OF cl[THEN conjunct1] cl[THEN conjunct2] declared declared' rows keys
          checked checked_roots restricted restricted_roots])
  then show ?thesis unfolding restricted_declaration_term_def declaration_term_def found .
qed

section \<open>On a constructed edit, the incremental call judges the answer state\<close>

text \<open>
  For the edit the constructor makes, the premises are the constructor's contract (\<open>state_edit_contract\<close>)
  and the request state's closedness, read through \<open>native_undeclared_exact\<close> on the request state; the
  whole call on the answer state is \<open>native_undeclared_exact\<close> again. Any lists of the families of the two
  states and of the added families serve, each computed once.
\<close>

corollary edited_undeclared_exact:
  assumes presented: "state_presenter S=Some R"
    and answer: "state_presentable (edit_applied S ns removed added)"
    and edit: "state_edit_of S ns removed added=Some e"
    and closed: "isabelle_undeclared_constants (fst S) (snd S)=[]"
    and families: "set Fs=range (state_entities R)"
    and families': "set Fs'=range (state_entities (edited_state R e))"
    and added_families: "set As=range (edit_added e)"
    and keys: "\<And>z d. z\<in>edit_rows (edit_removed e) \<Longrightarrow> d\<in>set (row_declared (snd z)) \<Longrightarrow> d\<in>set ks"
    and identity: "\<And>y. term_formed (ident y)" and roots: "\<And>y. term_formed (identr y)"
  shows "(verdict_undeclared,Pair_Term (restricted_declaration_term (edited_undeclared_keys
        (edited_undeclared_families As Fs' ks) (edited_undeclared_roots (state_roots R) ks)) Fs')
      (Pair_Term (state_families_term ident (edited_undeclared_families As Fs' ks))
        (state_family_term identr (edited_undeclared_roots (state_roots R) ks))))
      \<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    isabelle_undeclared_constants (fst (edit_applied S ns removed added)) (snd (edit_applied S ns removed added))=[]"
proof -
  have present: "state_presents state_constant_key S R" by (rule state_presenter_presents[OF presented])
  note contract = state_edit_contract[OF presented answer edit]
  have closed_call: "(verdict_undeclared,Pair_Term (declaration_term Fs) (Pair_Term (state_families_term ident Fs)
      (state_family_term identr (state_roots R))))\<in>positive_meaning verdict_mentions_system"
    using native_undeclared_exact[where ident=ident and identr=identr, OF present families identity roots] closed by blast
  have reduced: "presented_rows (edited_state R e)=(presented_rows R-edit_rows (edit_removed e)) \<union> edit_rows (edit_added e)"
    using contract(3) by (simp add: edit_reduced_def)
  have u1: "(\<Union>F\<in>set Fs. set F)=presented_rows R" using families by (auto simp: presented_rows_def)
  have u2: "(\<Union>F\<in>set Fs'. set F)=presented_rows (edited_state R e)"
    using families' by (auto simp: presented_rows_def)
  have u3: "(\<Union>F\<in>set As. set F)=edit_rows (edit_added e)" using added_families by (auto simp: edit_rows_def)
  have rows: "(\<Union>F\<in>set Fs'. set F)=(\<Union>F\<in>set Fs. set F)-edit_rows (edit_removed e) \<union> (\<Union>F\<in>set As. set F)"
    unfolding u1 u2 u3 by (rule reduced)
  have whole: "(verdict_undeclared,Pair_Term (declaration_term Fs') (Pair_Term (state_families_term ident Fs')
      (state_family_term identr (state_roots R))))\<in>positive_meaning verdict_mentions_system \<longleftrightarrow>
    isabelle_undeclared_constants (fst (edit_applied S ns removed added)) (snd (edit_applied S ns removed added))=[]"
    unfolding contract(4)[symmetric] by (rule native_undeclared_exact[where ident=ident and identr=identr, OF contract(1) families' identity roots])
  show ?thesis
    by (rule trans[OF edited_undeclared[where ident=ident and identr=identr, OF identity roots closed_call rows keys] whole])
qed

end
