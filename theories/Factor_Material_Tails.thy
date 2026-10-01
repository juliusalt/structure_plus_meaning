theory Factor_Material_Tails
  imports Factor_Material_Resolution Factor_Program_Resolution Factor_Shared_Patterns Factor_Resolution_Lifting
    Factor_Pattern_Regions Map_Filter_Lists
begin

section \<open>The spine of a pattern\<close>

text \<open>
  D3b1m of DECISIONS.md, task 495's entry, its addition "The chain's holders kept (D3', task 981)", (b). A material
  premise reads each of its four fields as a list along its spine, the chain of right children of pairs: its
  entries, the left children, each read by the field's entry reader, and its end, the first part that is no pair. The
  spine's tail is the variable ending it, if one does. A substitution that binds none of the entries' variables extends
  the spine by its tail's image and leaves the entries as they stand.
\<close>

fun finite_spine_entries :: "'a finite_term_pattern \<Rightarrow> 'a finite_term_pattern list" where
  "finite_spine_entries (Finite_Pattern_Pair p q) = p # finite_spine_entries q"
| "finite_spine_entries p = []"

fun finite_spine_end :: "'a finite_term_pattern \<Rightarrow> 'a finite_term_pattern" where
  "finite_spine_end (Finite_Pattern_Pair p q) = finite_spine_end q"
| "finite_spine_end p = p"

definition finite_spine_tail :: "'a finite_term_pattern \<Rightarrow> 'a option" where
  "finite_spine_tail p = (case finite_spine_end p of Finite_Variable a \<Rightarrow> Some a | _ \<Rightarrow> None)"

fun finite_spine_entry_variables :: "'a finite_term_pattern \<Rightarrow> 'a fset" where
  "finite_spine_entry_variables (Finite_Pattern_Pair p q) =
    finite_pattern_variables p |\<union>| finite_spine_entry_variables q"
| "finite_spine_entry_variables p = {||}"

definition finite_spine_graft :: "'a finite_term_pattern list \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'a finite_term_pattern" where
  "finite_spine_graft es t = foldr Finite_Pattern_Pair es t"

lemma finite_spine_graft_simps [simp]:
  "finite_spine_graft [] t = t"
  "finite_spine_graft (e # es) t = Finite_Pattern_Pair e (finite_spine_graft es t)"
  by (simp_all add: finite_spine_graft_def)

lemma finite_spine_tail_simps [simp]:
  "finite_spine_tail (Finite_Variable a) = Some a"
  "finite_spine_tail (Finite_Pattern_Target t) = None"
  "finite_spine_tail (Finite_Pattern_Payload v) = None"
  "finite_spine_tail (Finite_Pattern_Pair p q) = finite_spine_tail q"
  by (simp_all add: finite_spine_tail_def)

lemma finite_spine_end_not_pair: "finite_spine_end p \<noteq> Finite_Pattern_Pair x y"
  by (induction p) simp_all

lemma finite_spine_decompose: "finite_spine_graft (finite_spine_entries p) (finite_spine_end p) = p"
  by (induction p) simp_all

lemma finite_spine_graft_fields [simp]:
  "finite_spine_entries (finite_spine_graft es t) = es @ finite_spine_entries t"
  "finite_spine_end (finite_spine_graft es t) = finite_spine_end t"
  "finite_spine_tail (finite_spine_graft es t) = finite_spine_tail t"
  by (induction es) simp_all

lemma finite_spine_tail_end: "finite_spine_tail p = Some a \<longleftrightarrow> finite_spine_end p = Finite_Variable a"
  by (auto simp: finite_spine_tail_def split: finite_term_pattern.splits)

lemma finite_spine_end_cases:
  obtains (variable) a where "finite_spine_end p = Finite_Variable a" "finite_spine_tail p = Some a"
  | (leaf) "finite_spine_tail p = None" "finite_pattern_variables (finite_spine_end p) = {||}"
      "\<And>\<sigma>. finite_pattern_substitute \<sigma> (finite_spine_end p) = finite_spine_end p"
proof (cases "finite_spine_end p")
  case (Finite_Variable a)
  then show ?thesis by (rule variable) (simp add: finite_spine_tail_def Finite_Variable)
next
  case (Finite_Pattern_Target t)
  then show ?thesis by (intro leaf) (simp_all add: finite_spine_tail_def)
next
  case (Finite_Pattern_Payload v)
  then show ?thesis by (intro leaf) (simp_all add: finite_spine_tail_def)
next
  case (Finite_Pattern_Pair x y)
  then show ?thesis using finite_spine_end_not_pair by blast
qed

lemma finite_spine_entry_variables_member:
  "a |\<in>| finite_spine_entry_variables p \<longleftrightarrow> (\<exists>e\<in>set (finite_spine_entries p). a |\<in>| finite_pattern_variables e)"
  by (induction p) auto

lemma finite_spine_variables_member:
  "a |\<in>| finite_pattern_variables p \<longleftrightarrow>
    a |\<in>| finite_spine_entry_variables p \<or> a |\<in>| finite_pattern_variables (finite_spine_end p)"
  by (induction p) auto

lemma finite_spine_tail_variable: "finite_spine_tail p = Some a \<Longrightarrow> a |\<in>| finite_pattern_variables p"
proof -
  assume "finite_spine_tail p = Some a"
  then have "finite_spine_end p = Finite_Variable a" by (simp add: finite_spine_tail_end)
  then show ?thesis using finite_spine_variables_member[of a p] by simp
qed

lemma finite_spine_entry_variables_subset:
  "a |\<in>| finite_spine_entry_variables p \<Longrightarrow> a |\<in>| finite_pattern_variables p"
  using finite_spine_variables_member[of a p] by blast

lemma finite_spine_variable_cases:
  "a |\<in>| finite_pattern_variables p \<longleftrightarrow> a |\<in>| finite_spine_entry_variables p \<or> finite_spine_tail p = Some a"
  using finite_spine_variables_member[of a p] by (cases rule: finite_spine_end_cases[of p]) auto

lemma finite_spine_ground_tail:
  "finite_pattern_variables p = {||} \<Longrightarrow> finite_spine_tail p = None"
  using finite_spine_tail_variable[of p] by (cases "finite_spine_tail p") auto

lemma finite_spine_ground_entries:
  assumes "finite_pattern_variables p = {||}"
  shows "finite_spine_entry_variables p = {||}"
proof (rule fset_eqI)
  fix a
  show "a |\<in>| finite_spine_entry_variables p \<longleftrightarrow> a |\<in>| {||}"
    using finite_spine_entry_variables_subset[of a p] assms by auto
qed

lemma finite_spine_graft_entry_variables:
  "a |\<in>| finite_spine_entry_variables (finite_spine_graft es t) \<longleftrightarrow>
    (\<exists>e\<in>set es. a |\<in>| finite_pattern_variables e) \<or> a |\<in>| finite_spine_entry_variables t"
  by (induction es) auto

subsection \<open>Substitution along a spine\<close>

lemma finite_spine_substitute:
  "finite_pattern_substitute \<sigma> p = finite_spine_graft (map (finite_pattern_substitute \<sigma>) (finite_spine_entries p))
    (finite_pattern_substitute \<sigma> (finite_spine_end p))"
  by (induction p) simp_all

theorem finite_spine_substitute_fixed:
  assumes fixed: "\<And>a. a |\<in>| finite_spine_entry_variables p \<Longrightarrow> \<sigma> a = Finite_Variable a"
  shows "finite_pattern_substitute \<sigma> p =
    finite_spine_graft (finite_spine_entries p) (finite_pattern_substitute \<sigma> (finite_spine_end p))"
proof -
  have entries: "map (finite_pattern_substitute \<sigma>) (finite_spine_entries p) = finite_spine_entries p"
  proof (rule map_idI)
    fix e assume e: "e \<in> set (finite_spine_entries p)"
    have "finite_pattern_substitute \<sigma> e = finite_pattern_substitute Finite_Variable e"
    proof (rule finite_pattern_substitute_cong)
      fix a assume "a |\<in>| finite_pattern_variables e"
      with e have "a |\<in>| finite_spine_entry_variables p" unfolding finite_spine_entry_variables_member by blast
      then show "\<sigma> a = Finite_Variable a" by (rule fixed)
    qed
    then show "finite_pattern_substitute \<sigma> e = e" by simp
  qed
  show ?thesis using finite_spine_substitute[of \<sigma> p] unfolding entries .
qed

theorem finite_spine_tail_substitute:
  assumes tail: "finite_spine_tail p = Some a"
    and fixed: "\<And>b. b |\<in>| finite_spine_entry_variables p \<Longrightarrow> \<sigma> b = Finite_Variable b"
  shows "finite_pattern_substitute \<sigma> p = finite_spine_graft (finite_spine_entries p) (\<sigma> a)"
    and "finite_spine_entries (finite_pattern_substitute \<sigma> p) = finite_spine_entries p @ finite_spine_entries (\<sigma> a)"
    and "finite_spine_tail (finite_pattern_substitute \<sigma> p) = finite_spine_tail (\<sigma> a)"
proof -
  show eq: "finite_pattern_substitute \<sigma> p = finite_spine_graft (finite_spine_entries p) (\<sigma> a)"
    using finite_spine_substitute_fixed[OF fixed] tail by (simp add: finite_spine_tail_end)
  then show "finite_spine_entries (finite_pattern_substitute \<sigma> p) =
      finite_spine_entries p @ finite_spine_entries (\<sigma> a)" by simp
  from eq show "finite_spine_tail (finite_pattern_substitute \<sigma> p) = finite_spine_tail (\<sigma> a)" by simp
qed

section \<open>Readings along a spine\<close>

text \<open>
  A list read along a spine has no reading exactly where an entry has none or its end has none; where the
  spine ends in a variable and no entry lacks a reading, it is open, whatever the entries read.
\<close>

lemma finite_list_graft_unreadable:
  "finite_list_pattern_read z rd (finite_spine_graft es t) = Unreadable \<longleftrightarrow>
    (\<exists>e\<in>set es. rd e = Unreadable) \<or> finite_list_pattern_read z rd t = Unreadable"
  by (induction es) (auto simp: map_reading_cases reading_pair_unreadable_iff)

lemma finite_list_spine_unreadable:
  "finite_list_pattern_read z rd p = Unreadable \<longleftrightarrow>
    (\<exists>e\<in>set (finite_spine_entries p). rd e = Unreadable) \<or>
    finite_list_pattern_read z rd (finite_spine_end p) = Unreadable"
  using finite_list_graft_unreadable[of z rd "finite_spine_entries p" "finite_spine_end p"]
  by (simp add: finite_spine_decompose)

lemma finite_list_unreadable_cong:
  assumes "\<And>e. rd e = Unreadable \<longleftrightarrow> rd' e = Unreadable"
  shows "finite_list_pattern_read z rd p = Unreadable \<longleftrightarrow> finite_list_pattern_read z rd' p = Unreadable"
  by (induction p) (auto simp: map_reading_cases reading_pair_unreadable_iff assms)

theorem finite_list_tail_open:
  assumes "finite_spine_tail p \<noteq> None" "finite_list_pattern_read z rd p \<noteq> Unreadable"
  shows "finite_list_pattern_read z rd p = Open_Reading"
  using assms by (induction p) (auto simp: map_reading_cases reading_pair_open reading_pair_unreadable_iff)

corollary finite_list_tail_entries_open:
  assumes tail: "finite_spine_tail p \<noteq> None"
    and entries: "\<And>e. e \<in> set (finite_spine_entries p) \<Longrightarrow> rd e \<noteq> Unreadable"
  shows "finite_list_pattern_read z rd p = Open_Reading"
proof (rule finite_list_tail_open[OF tail])
  obtain a where "finite_spine_end p = Finite_Variable a"
    using tail by (cases "finite_spine_tail p") (auto simp: finite_spine_tail_end)
  then show "finite_list_pattern_read z rd p \<noteq> Unreadable"
    using entries by (auto simp: finite_list_spine_unreadable[of z rd p])
qed

section \<open>A material pattern's fields\<close>

text \<open>
  Each field is read as a list along its spine, at its terminator and by its entry reader: the atoms at the empty
  artifact's whole target by atom entries, the edges at the empty payload by incidence entries, the counts and the
  functions at the empty payload by attachment entries. A field's kind is its terminator and its entry reader, the
  reader's values forgotten: whether a field has no reading depends on its terminator and on which entries have none.
\<close>

type_synonym 'a material_field_kind = "finite_factor_term \<times> ('a finite_term_pattern \<Rightarrow> unit material_reading)"

definition finite_field_kind ::
    "finite_factor_term \<Rightarrow> ('a finite_term_pattern \<Rightarrow> 'x material_reading) \<Rightarrow> 'a material_field_kind" where
  "finite_field_kind z rd = (z, \<lambda>e. map_material_reading (\<lambda>_. ()) (rd e))"

definition finite_material_read_fields ::
    "'a finite_material_pattern \<Rightarrow> ('a material_field_kind \<times> 'a finite_term_pattern) list" where
  "finite_material_read_fields M = [
    (finite_field_kind (Finite_Target (Finite_Whole finite_empty_artifact)) finite_atom_entry, finite_material_atoms M),
    (finite_field_kind (Finite_Payload []) finite_incidence_entry, finite_material_edges M),
    (finite_field_kind (Finite_Payload []) finite_attachment_entry, finite_material_counts M),
    (finite_field_kind (Finite_Payload []) finite_attachment_entry, finite_material_functions M)]"

definition finite_material_spine_fields :: "'a finite_material_pattern \<Rightarrow> 'a finite_term_pattern list" where
  "finite_material_spine_fields M = map snd (finite_material_read_fields M)"

definition finite_field_entry_unreadable :: "'a material_field_kind \<Rightarrow> 'a finite_term_pattern \<Rightarrow> bool" where
  "finite_field_entry_unreadable k e \<longleftrightarrow> snd k e = Unreadable"

definition finite_field_unreadable :: "'a material_field_kind \<Rightarrow> 'a finite_term_pattern \<Rightarrow> bool" where
  "finite_field_unreadable k p \<longleftrightarrow> finite_list_pattern_read (fst k) (snd k) p = Unreadable"

lemma finite_field_kind_unreadable:
  "finite_field_unreadable (finite_field_kind z rd) p \<longleftrightarrow> finite_list_pattern_read z rd p = Unreadable"
  unfolding finite_field_unreadable_def finite_field_kind_def fst_conv snd_conv
  by (rule finite_list_unreadable_cong) (simp add: map_reading_cases)

lemma finite_field_unreadable_variable [simp]: "\<not> finite_field_unreadable k (Finite_Variable a)"
  by (simp add: finite_field_unreadable_def)

lemma finite_field_unreadable_graft:
  "finite_field_unreadable k (finite_spine_graft es t) \<longleftrightarrow>
    (\<exists>e\<in>set es. finite_field_entry_unreadable k e) \<or> finite_field_unreadable k t"
  by (simp add: finite_field_unreadable_def finite_field_entry_unreadable_def finite_list_graft_unreadable)

lemma finite_material_field_variable:
  "f \<in> set (finite_material_spine_fields M) \<Longrightarrow> a |\<in>| finite_pattern_variables f \<Longrightarrow> a |\<in>| finite_material_variables M"
  by (auto simp: finite_material_spine_fields_def finite_material_read_fields_def finite_material_variables_def)

theorem finite_material_skeleton_unreadable_fields:
  "finite_material_skeleton M = Unreadable \<longleftrightarrow>
    (\<exists>(k,f)\<in>set (finite_material_read_fields M). finite_field_unreadable k f)"
  by (auto simp: finite_material_skeleton_unreadable_iff finite_material_read_fields_def finite_field_kind_unreadable)

theorem finite_material_skeleton_open:
  assumes readable: "\<forall>(k,f)\<in>set (finite_material_read_fields M). \<not> finite_field_unreadable k f"
    and tail: "\<exists>f\<in>set (finite_material_spine_fields M). finite_spine_tail f \<noteq> None"
  shows "finite_material_skeleton M = Open_Reading"
proof -
  let ?a = "finite_enumeration_pattern_read finite_atom_entry (finite_material_atoms M)"
  let ?b = "finite_list_pattern_read (Finite_Payload []) finite_incidence_entry (finite_material_edges M)"
  let ?c = "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_counts M)"
  let ?d = "finite_list_pattern_read (Finite_Payload []) finite_attachment_entry (finite_material_functions M)"
  have u: "?a \<noteq> Unreadable" "?b \<noteq> Unreadable" "?c \<noteq> Unreadable" "?d \<noteq> Unreadable"
    using readable by (simp_all add: finite_material_read_fields_def finite_field_kind_unreadable)
  from tail obtain f where f: "f \<in> set (finite_material_spine_fields M)" "finite_spine_tail f \<noteq> None" by blast
  have "f = finite_material_atoms M \<or> f = finite_material_edges M \<or> f = finite_material_counts M \<or>
      f = finite_material_functions M"
    using f(1) by (simp add: finite_material_spine_fields_def finite_material_read_fields_def)
  then have "?a = Open_Reading \<or> ?b = Open_Reading \<or> ?c = Open_Reading \<or> ?d = Open_Reading"
  proof (elim disjE)
    assume "f = finite_material_atoms M"
    then show ?thesis using finite_list_tail_open[OF f(2), where z="Finite_Target (Finite_Whole finite_empty_artifact)"
      and rd=finite_atom_entry] u(1) by simp
  next
    assume "f = finite_material_edges M"
    then show ?thesis using finite_list_tail_open[OF f(2), where z="Finite_Payload []" and rd=finite_incidence_entry]
      u(2) by simp
  next
    assume "f = finite_material_counts M"
    then show ?thesis using finite_list_tail_open[OF f(2), where z="Finite_Payload []" and rd=finite_attachment_entry]
      u(3) by simp
  next
    assume "f = finite_material_functions M"
    then show ?thesis using finite_list_tail_open[OF f(2), where z="Finite_Payload []" and rd=finite_attachment_entry]
      u(4) by simp
  qed
  then show ?thesis using u
    by (auto simp: finite_material_skeleton_def map_reading_cases reading_pair_open reading_pair_unreadable_iff)
qed

section \<open>The tails of a material pattern\<close>

text \<open>
  The tails are the spine tails of the fields that stand at one position of the pattern only: in no entry of a
  field, not in the source, and ending one field. The notion is stated once over a view of a pattern (its variables,
  its spine tail and its entries' variables), so a finite pattern and a shared one read it alike.
\<close>


definition spine_tails_with ::
    "('p \<Rightarrow> 'a fset) \<Rightarrow> ('p \<Rightarrow> 'a option) \<Rightarrow> ('p \<Rightarrow> 'a fset) \<Rightarrow> 'p \<Rightarrow> 'p list \<Rightarrow> 'a fset" where
  "spine_tails_with V t E s fs = ffilter (\<lambda>a. a |\<notin>| V s \<and> (\<forall>f\<in>set fs. a |\<notin>| E f) \<and>
    length (filter (\<lambda>f. t f = Some a) fs) = 1) (fset_of_list (List.map_filter t fs))"

lemma spine_tails_with_member:
  "a |\<in>| spine_tails_with V t E s fs \<longleftrightarrow> (\<exists>f\<in>set fs. t f = Some a) \<and> a |\<notin>| V s \<and>
    (\<forall>f\<in>set fs. a |\<notin>| E f) \<and> length (filter (\<lambda>f. t f = Some a) fs) = 1"
  by (auto simp: spine_tails_with_def fset_of_list_elem map_filter_member)

lemma spine_tails_with_map:
  assumes "V' (h s) = V s" "\<And>f. f \<in> set fs \<Longrightarrow> t' (h f) = t f" "\<And>f. f \<in> set fs \<Longrightarrow> E' (h f) = E f"
  shows "spine_tails_with V' t' E' (h s) (map h fs) = spine_tails_with V t E s fs"
proof (rule fset_eqI)
  fix a
  have "filter (\<lambda>f. t' (h f) = Some a) fs = filter (\<lambda>f. t f = Some a) fs"
    by (rule filter_cong) (simp_all add: assms(2))
  then show "a |\<in>| spine_tails_with V' t' E' (h s) (map h fs) \<longleftrightarrow> a |\<in>| spine_tails_with V t E s fs"
    by (auto simp: spine_tails_with_member assms filter_map o_def)
qed

definition finite_spine_tails :: "'a finite_term_pattern \<Rightarrow> 'a finite_term_pattern list \<Rightarrow> 'a fset" where
  "finite_spine_tails = spine_tails_with finite_pattern_variables finite_spine_tail finite_spine_entry_variables"

definition finite_material_tails :: "'a finite_material_pattern \<Rightarrow> 'a fset" where
  "finite_material_tails M = finite_spine_tails (finite_material_source M) (finite_material_spine_fields M)"

lemma finite_material_tails_member:
  "a |\<in>| finite_material_tails M \<longleftrightarrow> (\<exists>f\<in>set (finite_material_spine_fields M). finite_spine_tail f = Some a) \<and>
    a |\<notin>| finite_pattern_variables (finite_material_source M) \<and>
    (\<forall>f\<in>set (finite_material_spine_fields M). a |\<notin>| finite_spine_entry_variables f) \<and>
    length (filter (\<lambda>f. finite_spine_tail f = Some a) (finite_material_spine_fields M)) = 1"
  by (simp add: finite_material_tails_def finite_spine_tails_def spine_tails_with_member)

lemma finite_material_tailsE:
  assumes "a |\<in>| finite_material_tails M"
  obtains f where "f \<in> set (finite_material_spine_fields M)" "finite_spine_tail f = Some a"
    "a |\<notin>| finite_pattern_variables (finite_material_source M)"
    "\<And>g. g \<in> set (finite_material_spine_fields M) \<Longrightarrow> a |\<notin>| finite_spine_entry_variables g"
    "length (filter (\<lambda>g. finite_spine_tail g = Some a) (finite_material_spine_fields M)) = 1"
proof -
  have m: "(\<exists>f\<in>set (finite_material_spine_fields M). finite_spine_tail f = Some a) \<and>
    a |\<notin>| finite_pattern_variables (finite_material_source M) \<and>
    (\<forall>g\<in>set (finite_material_spine_fields M). a |\<notin>| finite_spine_entry_variables g) \<and>
    length (filter (\<lambda>g. finite_spine_tail g = Some a) (finite_material_spine_fields M)) = 1"
    using finite_material_tails_member[THEN iffD1, OF assms] .
  from conjunct1[OF m] obtain f where f: "f \<in> set (finite_material_spine_fields M)" "finite_spine_tail f = Some a"
    by (rule bexE)
  show ?thesis
  proof (rule that[OF f])
    show "a |\<notin>| finite_pattern_variables (finite_material_source M)" by (rule conjunct1[OF conjunct2[OF m]])
    show "a |\<notin>| finite_spine_entry_variables g" if "g \<in> set (finite_material_spine_fields M)" for g
      by (rule bspec[OF conjunct1[OF conjunct2[OF conjunct2[OF m]]] that])
    show "length (filter (\<lambda>g. finite_spine_tail g = Some a) (finite_material_spine_fields M)) = 1"
      by (rule conjunct2[OF conjunct2[OF conjunct2[OF m]]])
  qed
qed

lemma finite_material_tails_variable: "a |\<in>| finite_material_tails M \<Longrightarrow> a |\<in>| finite_material_variables M"
  by (elim finite_material_tailsE)
    (rule finite_material_field_variable[OF _ finite_spine_tail_variable], assumption+)

definition finite_material_rebound_tails ::
    "('a \<Rightarrow> 'a finite_term_pattern) \<Rightarrow> 'a finite_material_pattern \<Rightarrow> 'a fset" where
  "finite_material_rebound_tails \<sigma> M = ffilter (\<lambda>a. \<sigma> a = Finite_Variable a \<and>
      (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> a |\<notin>| finite_pattern_variables (\<sigma> b)))
      (finite_material_tails M) |\<union>|
    (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"

lemma finite_material_rebound_tails_member:
  "x |\<in>| finite_material_rebound_tails \<sigma> M \<longleftrightarrow>
    (x |\<in>| finite_material_tails M \<and> \<sigma> x = Finite_Variable x \<and>
      (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> x |\<notin>| finite_pattern_variables (\<sigma> b))) \<or>
    (\<exists>a. a |\<in>| finite_material_tails M \<and> \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) = Some x)"
proof -
  have image: "x |\<in>| (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M) \<longleftrightarrow>
    (\<exists>a. a |\<in>| finite_material_tails M \<and> \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) = Some x)"
  proof
    assume "x |\<in>| (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"
    then obtain a where "x = the (finite_spine_tail (\<sigma> a))"
      "a |\<in>| ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"
      by (rule fimageE)
    then show "\<exists>a. a |\<in>| finite_material_tails M \<and> \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) = Some x"
      by (cases "finite_spine_tail (\<sigma> a)") auto
  next
    assume "\<exists>a. a |\<in>| finite_material_tails M \<and> \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) = Some x"
    then obtain a where a: "a |\<in>| finite_material_tails M" "\<sigma> a \<noteq> Finite_Variable a" "finite_spine_tail (\<sigma> a) = Some x"
      by blast
    then show "x |\<in>| (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"
      by (intro rev_fimage_eqI[of a]) auto
  qed
  show ?thesis unfolding finite_material_rebound_tails_def funion_iff image by auto
qed

section \<open>A waiting material premise kept across a binding of its tails\<close>

text \<open>
  A substitution that binds no variable of a material pattern but its tails leaves its source and every entry as
  they stand and extends each bound field's spine by its tail's image. If the pattern waits, every image read along
  its spine by its field's entry reader has a reading or is open, and some field still ends in a variable, the
  substituted pattern waits: its source is unchanged, no field lacks a reading (the anchors' independence), and the
  field ending in a variable is open. Its tails are the unbound tails no image holds, with the images' own tails.
\<close>

locale material_tail_binding =
  fixes M :: "'a finite_material_pattern" and \<sigma> :: "'a \<Rightarrow> 'a finite_term_pattern"
  assumes binds: "\<And>a. a |\<in>| finite_material_variables M \<Longrightarrow> \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow>
    a |\<in>| finite_material_tails M"
begin

lemma unbound_variable:
  "a |\<in>| finite_material_variables M \<Longrightarrow> a |\<notin>| finite_material_tails M \<Longrightarrow> \<sigma> a = Finite_Variable a"
  using binds by blast

lemma source_fixed: "finite_pattern_substitute \<sigma> (finite_material_source M) = finite_material_source M"
proof -
  have "finite_pattern_substitute \<sigma> (finite_material_source M) =
      finite_pattern_substitute Finite_Variable (finite_material_source M)"
  proof (rule finite_pattern_substitute_cong)
    fix a assume a: "a |\<in>| finite_pattern_variables (finite_material_source M)"
    then have "a |\<in>| finite_material_variables M" by (simp add: finite_material_variables_def)
    moreover have "a |\<notin>| finite_material_tails M" using a by (auto elim: finite_material_tailsE)
    ultimately show "\<sigma> a = Finite_Variable a" by (rule unbound_variable)
  qed
  then show ?thesis by simp
qed

lemma entries_fixed:
  assumes f: "f \<in> set (finite_material_spine_fields M)" and a: "a |\<in>| finite_spine_entry_variables f"
  shows "\<sigma> a = Finite_Variable a"
proof (rule unbound_variable)
  show "a |\<in>| finite_material_variables M"
    by (rule finite_material_field_variable[OF f finite_spine_entry_variables_subset[OF a]])
  show "a |\<notin>| finite_material_tails M" using f a by (auto elim: finite_material_tailsE)
qed

lemma field_substitute:
  assumes f: "f \<in> set (finite_material_spine_fields M)"
  shows "finite_pattern_substitute \<sigma> f =
    finite_spine_graft (finite_spine_entries f) (finite_pattern_substitute \<sigma> (finite_spine_end f))"
  by (rule finite_spine_substitute_fixed) (rule entries_fixed[OF f])

lemma tail_bound:
  assumes "f \<in> set (finite_material_spine_fields M)" "finite_spine_tail f = Some b" "\<sigma> b \<noteq> Finite_Variable b"
  shows "b |\<in>| finite_material_tails M"
  by (rule binds[OF finite_material_field_variable[OF assms(1) finite_spine_tail_variable[OF assms(2)]] assms(3)])

lemma field_tail_cases:
  assumes f: "f \<in> set (finite_material_spine_fields M)"
  obtains (kept) a where "finite_spine_tail f = Some a" "\<sigma> a = Finite_Variable a" "finite_pattern_substitute \<sigma> f = f"
  | (bound) a where "finite_spine_tail f = Some a" "\<sigma> a \<noteq> Finite_Variable a" "a |\<in>| finite_material_tails M"
      "finite_pattern_substitute \<sigma> f = finite_spine_graft (finite_spine_entries f) (\<sigma> a)"
  | (closed) "finite_spine_tail f = None" "finite_pattern_substitute \<sigma> f = f"
proof (cases rule: finite_spine_end_cases[of f])
  case (variable a)
  have eq: "finite_pattern_substitute \<sigma> f = finite_spine_graft (finite_spine_entries f) (\<sigma> a)"
    using field_substitute[OF f] variable by simp
  show ?thesis
  proof (cases "\<sigma> a = Finite_Variable a")
    case True
    then have "finite_pattern_substitute \<sigma> f = f"
      using eq variable(1) finite_spine_decompose[of f] by simp
    then show ?thesis using kept variable(2) True by blast
  next
    case False
    have "a |\<in>| finite_material_tails M" by (rule tail_bound[OF f variable(2) False])
    then show ?thesis using bound variable(2) False eq by blast
  qed
next
  case leaf
  have "finite_pattern_substitute \<sigma> f = f"
    using field_substitute[OF f] finite_spine_decompose[of f] leaf(3) by simp
  then show ?thesis using closed leaf(1) by blast
qed

lemma substitute_tail:
  assumes f: "f \<in> set (finite_material_spine_fields M)"
  shows "finite_spine_tail (finite_pattern_substitute \<sigma> f) =
    (case finite_spine_tail f of Some b \<Rightarrow> finite_spine_tail (\<sigma> b) | None \<Rightarrow> None)"
  by (cases rule: field_tail_cases[OF f, case_names kept bound closed]) simp_all

lemma substitute_entry_variables:
  assumes f: "f \<in> set (finite_material_spine_fields M)"
  shows "x |\<in>| finite_spine_entry_variables (finite_pattern_substitute \<sigma> f) \<longleftrightarrow>
    x |\<in>| finite_spine_entry_variables f \<or>
    (\<exists>b. finite_spine_tail f = Some b \<and> \<sigma> b \<noteq> Finite_Variable b \<and> x |\<in>| finite_spine_entry_variables (\<sigma> b))"
proof (cases rule: field_tail_cases[OF f, case_names kept bound closed])
  case (kept a) then show ?thesis by auto
next
  case (bound a)
  then show ?thesis by (auto simp: finite_spine_graft_entry_variables finite_spine_entry_variables_member)
next
  case closed then show ?thesis by auto
qed

lemma field_readable:
  assumes waits: "finite_material_resolution M = Material_Waits"
    and kf: "(k,f) \<in> set (finite_material_read_fields M)"
    and image: "\<And>a. finite_spine_tail f = Some a \<Longrightarrow> \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow>
      \<not> finite_field_unreadable k (\<sigma> a)"
  shows "\<not> finite_field_unreadable k (finite_pattern_substitute \<sigma> f)"
proof -
  have f: "f \<in> set (finite_material_spine_fields M)" using kf by (force simp: finite_material_spine_fields_def)
  have skel: "finite_material_skeleton M = Open_Reading" using waits by (simp add: finite_material_resolution_waits)
  then have nf: "\<not> finite_field_unreadable k f"
    using kf finite_material_skeleton_unreadable_fields[of M] by auto
  then have entries: "\<not> (\<exists>e\<in>set (finite_spine_entries f). finite_field_entry_unreadable k e)"
    using finite_field_unreadable_graft[of k "finite_spine_entries f" "finite_spine_end f"]
    by (auto simp: finite_spine_decompose)
  show ?thesis
  proof (cases rule: field_tail_cases[OF f, case_names kept bound closed])
    case (kept a) then show ?thesis using nf by simp
  next
    case (bound a)
    then show ?thesis using entries image[OF bound(1,2)] by (simp add: finite_field_unreadable_graft)
  next
    case closed then show ?thesis using nf by simp
  qed
qed

theorem waits_kept:
  assumes waits: "finite_material_resolution M = Material_Waits"
    and images: "\<And>k f a. (k,f) \<in> set (finite_material_read_fields M) \<Longrightarrow> finite_spine_tail f = Some a \<Longrightarrow>
      \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow> \<not> finite_field_unreadable k (\<sigma> a)"
    and open_tail: "\<exists>f\<in>set (finite_material_spine_fields (finite_material_pattern_substitute \<sigma> M)).
      finite_spine_tail f \<noteq> None"
  shows "finite_material_resolution (finite_material_pattern_substitute \<sigma> M) = Material_Waits"
    and "finite_material_alternative_set (finite_material_pattern_substitute \<sigma> M) = {||}"
proof -
  let ?N = "finite_material_pattern_substitute \<sigma> M"
  have readable_at: "\<not> finite_field_unreadable k (finite_pattern_substitute \<sigma> f)"
    if kf: "(k,f) \<in> set (finite_material_read_fields M)" for k f
    using waits kf by (rule field_readable) (rule images[OF kf])
  have readable: "\<forall>(k,f)\<in>set (finite_material_read_fields ?N). \<not> finite_field_unreadable k f"
    using readable_at by (simp add: finite_material_read_fields_def finite_material_pattern_substitute_def)
  have source: "finite_material_source ?N = finite_material_source M"
    using source_fixed by (simp add: finite_material_pattern_substitute_def)
  have "finite_material_skeleton ?N = Open_Reading" by (rule finite_material_skeleton_open[OF readable open_tail])
  moreover have "finite_pattern_variables (finite_material_source M) \<noteq> {||}"
    using waits by (simp add: finite_material_resolution_waits)
  ultimately show res: "finite_material_resolution ?N = Material_Waits"
    using source by (simp add: finite_material_resolution_waits)
  then show "finite_material_alternative_set ?N = {||}" by (simp add: finite_material_alternative_set_def)
qed

theorem tails_substitute:
  assumes fresh: "\<And>a c. a |\<in>| finite_material_tails M \<Longrightarrow> \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow>
      finite_spine_tail (\<sigma> a) = Some c \<Longrightarrow>
      c |\<notin>| finite_material_variables M \<and> c |\<notin>| finite_spine_entry_variables (\<sigma> a) \<and>
      (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> b \<noteq> a \<longrightarrow>
        c |\<notin>| finite_pattern_variables (\<sigma> b))"
  shows "finite_material_tails (finite_material_pattern_substitute \<sigma> M) = finite_material_rebound_tails \<sigma> M"
proof (rule fset_eqI)
  fix x
  let ?N = "finite_material_pattern_substitute \<sigma> M"
  let ?fs = "finite_material_spine_fields M"
  have fs': "finite_material_spine_fields ?N = map (finite_pattern_substitute \<sigma>) ?fs"
    by (simp add: finite_material_spine_fields_def finite_material_read_fields_def finite_material_pattern_substitute_def)
  have src: "finite_material_source ?N = finite_material_source M"
    using source_fixed by (simp add: finite_material_pattern_substitute_def)
  have count: "length (filter (\<lambda>f. finite_spine_tail f = Some x) (finite_material_spine_fields ?N)) =
      length (filter (\<lambda>f. finite_spine_tail f = Some y) ?fs)"
    if same: "\<And>f. f \<in> set ?fs \<Longrightarrow>
      (finite_spine_tail (finite_pattern_substitute \<sigma> f) = Some x) = (finite_spine_tail f = Some y)" for y
  proof -
    have "filter (\<lambda>f. finite_spine_tail (finite_pattern_substitute \<sigma> f) = Some x) ?fs =
        filter (\<lambda>f. finite_spine_tail f = Some y) ?fs"
      by (rule filter_cong[OF refl]) (erule same)
    then show ?thesis by (simp add: fs' filter_map o_def)
  qed
  have image_in: "finite_pattern_substitute \<sigma> f \<in> set (finite_material_spine_fields ?N)" if "f \<in> set ?fs" for f
    using that by (auto simp: fs')
  have left: "x |\<in>| finite_material_tails ?N"
    if x: "x |\<in>| finite_material_tails M" "\<sigma> x = Finite_Variable x"
      and apart: "\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow>
        x |\<notin>| finite_pattern_variables (\<sigma> b)"
  proof -
    from x(1) obtain f where f: "f \<in> set ?fs" "finite_spine_tail f = Some x"
      and src_x: "x |\<notin>| finite_pattern_variables (finite_material_source M)"
      and entries_x: "\<And>g. g \<in> set ?fs \<Longrightarrow> x |\<notin>| finite_spine_entry_variables g"
      and one: "length (filter (\<lambda>g. finite_spine_tail g = Some x) ?fs) = 1"
      by (elim finite_material_tailsE) blast
    have same: "(finite_spine_tail (finite_pattern_substitute \<sigma> g) = Some x) = (finite_spine_tail g = Some x)"
      if g: "g \<in> set ?fs" for g
    proof (cases "finite_spine_tail g")
      case None then show ?thesis using substitute_tail[OF g] by simp
    next
      case (Some b)
      show ?thesis
      proof (cases "\<sigma> b = Finite_Variable b")
        case True then show ?thesis using substitute_tail[OF g] Some by simp
      next
        case False
        have "b |\<in>| finite_material_tails M" by (rule tail_bound[OF g Some False])
        then have "x |\<notin>| finite_pattern_variables (\<sigma> b)" using apart False by blast
        then have "finite_spine_tail (\<sigma> b) \<noteq> Some x" using finite_spine_tail_variable[of "\<sigma> b" x] by auto
        moreover have "b \<noteq> x" using False x(2) by blast
        ultimately show ?thesis using substitute_tail[OF g] Some by simp
      qed
    qed
    show ?thesis unfolding finite_material_tails_member
    proof (intro conjI)
      show "\<exists>f'\<in>set (finite_material_spine_fields ?N). finite_spine_tail f' = Some x"
        using image_in[OF f(1)] same[OF f(1)] f(2) by blast
      show "x |\<notin>| finite_pattern_variables (finite_material_source ?N)" using src_x src by simp
      show "\<forall>g'\<in>set (finite_material_spine_fields ?N). x |\<notin>| finite_spine_entry_variables g'"
      proof
        fix g' assume "g' \<in> set (finite_material_spine_fields ?N)"
        then have "g' \<in> finite_pattern_substitute \<sigma> ` set ?fs" by (simp only: fs' set_map)
        then obtain g where g: "g \<in> set ?fs" "g' = finite_pattern_substitute \<sigma> g" by blast
        have "x |\<notin>| finite_spine_entry_variables (\<sigma> b)"
          if "finite_spine_tail g = Some b" "\<sigma> b \<noteq> Finite_Variable b" for b
          using apart[rule_format, OF tail_bound[OF g(1) that] that(2)]
            finite_spine_entry_variables_subset[of x "\<sigma> b"] by blast
        then show "x |\<notin>| finite_spine_entry_variables g'"
          unfolding g(2) substitute_entry_variables[OF g(1)] using entries_x[OF g(1)] by blast
      qed
      show "length (filter (\<lambda>f'. finite_spine_tail f' = Some x) (finite_material_spine_fields ?N)) = 1"
        using count[OF same] one by simp
    qed
  qed
  have right: "x |\<in>| finite_material_tails ?N"
    if a: "a |\<in>| finite_material_tails M" "\<sigma> a \<noteq> Finite_Variable a" "finite_spine_tail (\<sigma> a) = Some x" for a
  proof -
    from fresh[OF a] have xM: "x |\<notin>| finite_material_variables M"
      and xe: "x |\<notin>| finite_spine_entry_variables (\<sigma> a)"
      and xo: "\<And>b. b |\<in>| finite_material_tails M \<Longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<Longrightarrow> b \<noteq> a \<Longrightarrow>
        x |\<notin>| finite_pattern_variables (\<sigma> b)"
      by auto
    from a(1) obtain f where f: "f \<in> set ?fs" "finite_spine_tail f = Some a"
      and "a |\<notin>| finite_pattern_variables (finite_material_source M)"
      and "\<And>g. g \<in> set ?fs \<Longrightarrow> a |\<notin>| finite_spine_entry_variables g"
      and one: "length (filter (\<lambda>g. finite_spine_tail g = Some a) ?fs) = 1"
      by (elim finite_material_tailsE) blast
    have same: "(finite_spine_tail (finite_pattern_substitute \<sigma> g) = Some x) = (finite_spine_tail g = Some a)"
      if g: "g \<in> set ?fs" for g
    proof (cases "finite_spine_tail g")
      case None then show ?thesis using substitute_tail[OF g] by simp
    next
      case (Some b)
      show ?thesis
      proof (cases "\<sigma> b = Finite_Variable b")
        case True
        have "b |\<in>| finite_material_variables M"
          by (rule finite_material_field_variable[OF g finite_spine_tail_variable[OF Some]])
        then have "b \<noteq> x" using xM by blast
        moreover have "b \<noteq> a" using True a(2) by blast
        ultimately show ?thesis using substitute_tail[OF g] Some True by simp
      next
        case False
        show ?thesis
        proof (cases "b = a")
          case True then show ?thesis using substitute_tail[OF g] Some a(3) by simp
        next
          case ba: False
          have "x |\<notin>| finite_pattern_variables (\<sigma> b)" by (rule xo[OF tail_bound[OF g Some False] False ba])
          then have "finite_spine_tail (\<sigma> b) \<noteq> Some x" using finite_spine_tail_variable[of "\<sigma> b" x] by auto
          then show ?thesis using substitute_tail[OF g] Some ba by simp
        qed
      qed
    qed
    show ?thesis unfolding finite_material_tails_member
    proof (intro conjI)
      show "\<exists>f'\<in>set (finite_material_spine_fields ?N). finite_spine_tail f' = Some x"
        using image_in[OF f(1)] same[OF f(1)] f(2) by blast
      show "x |\<notin>| finite_pattern_variables (finite_material_source ?N)"
        using xM src by (auto simp: finite_material_variables_def)
      show "\<forall>g'\<in>set (finite_material_spine_fields ?N). x |\<notin>| finite_spine_entry_variables g'"
      proof
        fix g' assume "g' \<in> set (finite_material_spine_fields ?N)"
        then have "g' \<in> finite_pattern_substitute \<sigma> ` set ?fs" by (simp only: fs' set_map)
        then obtain g where g: "g \<in> set ?fs" "g' = finite_pattern_substitute \<sigma> g" by blast
        have "x |\<notin>| finite_spine_entry_variables g"
          using xM finite_material_field_variable[OF g(1) finite_spine_entry_variables_subset[of x g]] by blast
        moreover have "x |\<notin>| finite_spine_entry_variables (\<sigma> b)"
          if b: "finite_spine_tail g = Some b" "\<sigma> b \<noteq> Finite_Variable b" for b
        proof (cases "b = a")
          case True then show ?thesis using xe by simp
        next
          case False then show ?thesis
            using xo[OF tail_bound[OF g(1) b] b(2) False] finite_spine_entry_variables_subset[of x "\<sigma> b"]
            by blast
        qed
        ultimately show "x |\<notin>| finite_spine_entry_variables g'"
          unfolding g(2) substitute_entry_variables[OF g(1)] by blast
      qed
      show "length (filter (\<lambda>f'. finite_spine_tail f' = Some x) (finite_material_spine_fields ?N)) = 1"
        using count[OF same] one by simp
    qed
  qed
  have origin: "(x |\<in>| finite_material_tails M \<and> \<sigma> x = Finite_Variable x \<and>
      (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> x |\<notin>| finite_pattern_variables (\<sigma> b))) \<or>
      (\<exists>a. a |\<in>| finite_material_tails M \<and> \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) = Some x)"
    if xN: "x |\<in>| finite_material_tails ?N"
  proof -
    from xN obtain f' where f': "f' \<in> set (finite_material_spine_fields ?N)" "finite_spine_tail f' = Some x"
      and src_x: "x |\<notin>| finite_pattern_variables (finite_material_source ?N)"
      and entries_x: "\<And>g'. g' \<in> set (finite_material_spine_fields ?N) \<Longrightarrow> x |\<notin>| finite_spine_entry_variables g'"
      and one: "length (filter (\<lambda>g'. finite_spine_tail g' = Some x) (finite_material_spine_fields ?N)) = 1"
      by (elim finite_material_tailsE) blast
    from f'(1) have "f' \<in> finite_pattern_substitute \<sigma> ` set ?fs" by (simp only: fs' set_map)
    then obtain f where f: "f \<in> set ?fs" and f'_eq: "f' = finite_pattern_substitute \<sigma> f" by blast
    have entries_g: "x |\<notin>| finite_spine_entry_variables g \<and>
        (\<forall>b. finite_spine_tail g = Some b \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow>
          x |\<notin>| finite_spine_entry_variables (\<sigma> b))"
      if g: "g \<in> set ?fs" for g
      using entries_x[OF image_in[OF g]] unfolding substitute_entry_variables[OF g] by blast
    show ?thesis
    proof (cases rule: field_tail_cases[OF f, case_names kept bound closed])
      case (bound a)
      then show ?thesis using f'(2) f'_eq by auto
    next
      case closed
      then show ?thesis using f'(2) f'_eq by simp
    next
      case (kept a)
      have xa: "x = a" using kept f'(2) f'_eq by simp
      have xM: "x |\<in>| finite_material_variables M"
        using finite_material_field_variable[OF f finite_spine_tail_variable[OF kept(1)]] xa by simp
      have no_image_tail: "finite_spine_tail (\<sigma> b) \<noteq> Some x"
        if "b |\<in>| finite_material_tails M" "\<sigma> b \<noteq> Finite_Variable b" for b
        using fresh[OF that, of x] xM by blast
      have same: "(finite_spine_tail (finite_pattern_substitute \<sigma> g) = Some x) = (finite_spine_tail g = Some x)"
        if g: "g \<in> set ?fs" for g
      proof (cases "finite_spine_tail g")
        case None then show ?thesis using substitute_tail[OF g] by simp
      next
        case (Some b)
        show ?thesis
        proof (cases "\<sigma> b = Finite_Variable b")
          case True then show ?thesis using substitute_tail[OF g] Some by simp
        next
          case False
          have "finite_spine_tail (\<sigma> b) \<noteq> Some x" by (rule no_image_tail[OF tail_bound[OF g Some False] False])
          moreover have "b \<noteq> x" using False kept(2) xa by blast
          ultimately show ?thesis using substitute_tail[OF g] Some by simp
        qed
      qed
      have "x |\<in>| finite_material_tails M"
        unfolding finite_material_tails_member
      proof (intro conjI)
        show "\<exists>g\<in>set ?fs. finite_spine_tail g = Some x" using f kept(1) xa by blast
        show "x |\<notin>| finite_pattern_variables (finite_material_source M)" using src_x src by simp
        show "\<forall>g\<in>set ?fs. x |\<notin>| finite_spine_entry_variables g" using entries_g by blast
        show "length (filter (\<lambda>g. finite_spine_tail g = Some x) ?fs) = 1" using count[OF same] one by simp
      qed
      moreover have "x |\<notin>| finite_pattern_variables (\<sigma> b)"
        if b: "b |\<in>| finite_material_tails M" "\<sigma> b \<noteq> Finite_Variable b" for b
      proof -
        from b(1) obtain g where g: "g \<in> set ?fs" "finite_spine_tail g = Some b"
          and "b |\<notin>| finite_pattern_variables (finite_material_source M)"
          and "\<And>g. g \<in> set ?fs \<Longrightarrow> b |\<notin>| finite_spine_entry_variables g"
          and "length (filter (\<lambda>g. finite_spine_tail g = Some b) ?fs) = 1"
          by (elim finite_material_tailsE) blast
        have "x |\<notin>| finite_spine_entry_variables (\<sigma> b)" using entries_g[OF g(1)] g(2) b(2) by blast
        moreover have "finite_spine_tail (\<sigma> b) \<noteq> Some x" by (rule no_image_tail[OF b])
        ultimately show ?thesis using finite_spine_variable_cases[of x "\<sigma> b"] by blast
      qed
      ultimately show ?thesis using kept(2) xa by blast
    qed
  qed
  show "x |\<in>| finite_material_tails ?N \<longleftrightarrow> x |\<in>| finite_material_rebound_tails \<sigma> M"
    unfolding finite_material_rebound_tails_member using left right origin by blast
qed

corollary tails_substitute_apart:
  assumes fresh: "\<And>a c. a |\<in>| finite_material_tails M \<Longrightarrow> \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow>
      finite_spine_tail (\<sigma> a) = Some c \<Longrightarrow>
      c |\<notin>| finite_material_variables M \<and> c |\<notin>| finite_spine_entry_variables (\<sigma> a) \<and>
      (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow> \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> b \<noteq> a \<longrightarrow>
        c |\<notin>| finite_pattern_variables (\<sigma> b))"
    and apart: "\<And>a b. a |\<in>| finite_material_tails M \<Longrightarrow> \<sigma> a \<noteq> Finite_Variable a \<Longrightarrow>
      b |\<in>| finite_material_variables M \<Longrightarrow> b |\<notin>| finite_pattern_variables (\<sigma> a)"
  shows "finite_material_tails (finite_material_pattern_substitute \<sigma> M) =
    ffilter (\<lambda>a. \<sigma> a = Finite_Variable a) (finite_material_tails M) |\<union>|
    (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"
proof -
  have "ffilter (\<lambda>a. \<sigma> a = Finite_Variable a \<and> (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow>
      \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> a |\<notin>| finite_pattern_variables (\<sigma> b))) (finite_material_tails M) =
    ffilter (\<lambda>a. \<sigma> a = Finite_Variable a) (finite_material_tails M)"
  proof (rule fset_eqI)
    fix a
    show "a |\<in>| ffilter (\<lambda>a. \<sigma> a = Finite_Variable a \<and> (\<forall>b. b |\<in>| finite_material_tails M \<longrightarrow>
        \<sigma> b \<noteq> Finite_Variable b \<longrightarrow> a |\<notin>| finite_pattern_variables (\<sigma> b))) (finite_material_tails M) \<longleftrightarrow>
      a |\<in>| ffilter (\<lambda>a. \<sigma> a = Finite_Variable a) (finite_material_tails M)"
      using apart finite_material_tails_variable[of a M] by auto
  qed
  note filters = this
  have "finite_material_rebound_tails \<sigma> M =
    ffilter (\<lambda>a. \<sigma> a = Finite_Variable a) (finite_material_tails M) |\<union>|
    (\<lambda>a. the (finite_spine_tail (\<sigma> a))) |`|
      ffilter (\<lambda>a. \<sigma> a \<noteq> Finite_Variable a \<and> finite_spine_tail (\<sigma> a) \<noteq> None) (finite_material_tails M)"
    unfolding finite_material_rebound_tails_def filters by (rule refl)
  with tails_substitute[OF fresh] show ?thesis by (rule trans)
qed

end

section \<open>A canonical solution is never a waiting one\<close>

theorem finite_canonical_solutions_not_waiting:
  "finite_canonical_solutions M \<noteq> None \<Longrightarrow> finite_material_resolution M \<noteq> Material_Waits"
  by (auto simp: finite_canonical_solutions_def finite_material_resolution_waits
      split: finite_term_pattern.splits finite_exact_target.splits if_splits)

section \<open>The shared reads\<close>

text \<open>
  A shared pattern's spine is walked as its projection's: the walk stops at a reference, which is ground and ends no
  spine in a variable. Its entries' variables are read from the caches of its nodes, so the tails of a material
  premise held as shared patterns are read along each field's spine without a projection. An image is read along
  its spine by projecting each entry; a reference on its spine is ground and read once through its projection.
\<close>

fun shared_spine_tail :: "'a shared_pattern \<Rightarrow> 'a option" where
  "shared_spine_tail (Shared_Variable a) = Some a"
| "shared_spine_tail (Shared_Ground i) = None"
| "shared_spine_tail (Shared_Node A p q) = shared_spine_tail q"

fun shared_spine_entry_variables :: "'a shared_pattern \<Rightarrow> 'a fset" where
  "shared_spine_entry_variables (Shared_Node A p q) = shared_pattern_variables p |\<union>| shared_spine_entry_variables q"
| "shared_spine_entry_variables s = {||}"


lemma shared_spine_tail_project [simp]: "finite_spine_tail (shared_pattern_project T s) = shared_spine_tail s"
proof (induction s)
  case (Shared_Ground i)
  show ?case unfolding shared_spine_tail.simps by (rule finite_spine_ground_tail[OF shared_ground_project_variables])
qed simp_all

lemma shared_spine_entry_variables_project:
  "shared_pattern_formed T s \<Longrightarrow> shared_spine_entry_variables s = finite_spine_entry_variables (shared_pattern_project T s)"
proof (induction s)
  case (Shared_Ground i)
  show ?case unfolding shared_spine_entry_variables.simps
    by (rule finite_spine_ground_entries[OF shared_ground_project_variables, symmetric])
next
  case (Shared_Node A p q)
  then have "shared_pattern_formed T p" "shared_pattern_formed T q" by simp_all
  with Shared_Node.IH show ?case by (simp add: shared_pattern_variables_project)
qed simp

definition shared_spine_tails :: "'a shared_pattern \<Rightarrow> 'a shared_pattern list \<Rightarrow> 'a fset" where
  "shared_spine_tails = spine_tails_with shared_pattern_variables shared_spine_tail shared_spine_entry_variables"

theorem shared_spine_tails_project:
  assumes "shared_pattern_formed T s" "\<And>f. f \<in> set fs \<Longrightarrow> shared_pattern_formed T f"
  shows "shared_spine_tails s fs = finite_spine_tails (shared_pattern_project T s) (map (shared_pattern_project T) fs)"
proof -
  have "spine_tails_with finite_pattern_variables finite_spine_tail finite_spine_entry_variables
      (shared_pattern_project T s) (map (shared_pattern_project T) fs) =
    spine_tails_with shared_pattern_variables shared_spine_tail shared_spine_entry_variables s fs"
  proof (rule spine_tails_with_map[where h = "shared_pattern_project T"])
    show "finite_pattern_variables (shared_pattern_project T s) = shared_pattern_variables s"
      using shared_pattern_variables_project[OF assms(1)] by simp
    show "finite_spine_tail (shared_pattern_project T f) = shared_spine_tail f" if "f \<in> set fs" for f
      by simp
    show "finite_spine_entry_variables (shared_pattern_project T f) = shared_spine_entry_variables f"
      if "f \<in> set fs" for f
      using shared_spine_entry_variables_project[OF assms(2)[OF that]] by simp
  qed
  then show ?thesis by (simp add: shared_spine_tails_def finite_spine_tails_def)
qed

fun shared_list_read :: "finite_factor_term \<Rightarrow> ('a finite_term_pattern \<Rightarrow> 'x material_reading) \<Rightarrow> shape list \<Rightarrow>
    'a shared_pattern \<Rightarrow> 'x list material_reading" where
  "shared_list_read z rd T (Shared_Variable a) = Open_Reading"
| "shared_list_read z rd T (Shared_Ground i) =
    finite_list_pattern_read z rd (shared_pattern_project T (Shared_Ground i))"
| "shared_list_read z rd T (Shared_Node A p q) = map_material_reading (\<lambda>(x,xs). x#xs)
    (reading_pair (rd (shared_pattern_project T p)) (shared_list_read z rd T q))"

theorem shared_list_read_project:
  "shared_list_read z rd T s = finite_list_pattern_read z rd (shared_pattern_project T s)"
  by (induction s) simp_all

definition shared_field_unreadable :: "'a material_field_kind \<Rightarrow> shape list \<Rightarrow> 'a shared_pattern \<Rightarrow> bool" where
  "shared_field_unreadable k T s \<longleftrightarrow> shared_list_read (fst k) (snd k) T s = Unreadable"

theorem shared_field_unreadable_project:
  "shared_field_unreadable k T s \<longleftrightarrow> finite_field_unreadable k (shared_pattern_project T s)"
  by (simp add: shared_field_unreadable_def finite_field_unreadable_def shared_list_read_project)

end
