theory Factor_Pattern_Regions
  imports Factor_Program_Resolution Factor_Shared_Patterns
begin

section \<open>The positions of a finite pattern\<close>

text \<open>
  A position of a finite pattern is a path of directions from its root, @{const False} into a pair's first
  component and @{const True} into its second. A pattern has a subterm at each of its positions and none past
  a variable or a leaf. Positions are compared for equality and by prefix; no order of them is read.
\<close>

fun finite_pattern_at :: "'a finite_term_pattern \<Rightarrow> bool list \<Rightarrow> 'a finite_term_pattern option" where
  "finite_pattern_at p [] = Some p"
| "finite_pattern_at (Finite_Pattern_Pair p q) (d # w) = finite_pattern_at (if d then q else p) w"
| "finite_pattern_at p (d # w) = None"

lemma finite_pattern_at_leaves [simp]:
  "finite_pattern_at (Finite_Variable a) w = (if w = [] then Some (Finite_Variable a) else None)"
  "finite_pattern_at (Finite_Pattern_Target t) w = (if w = [] then Some (Finite_Pattern_Target t) else None)"
  "finite_pattern_at (Finite_Pattern_Payload v) w = (if w = [] then Some (Finite_Pattern_Payload v) else None)"
  by (cases w; simp)+

lemma finite_pattern_at_append:
  "finite_pattern_at p (u @ v) = (case finite_pattern_at p u of None \<Rightarrow> None | Some s \<Rightarrow> finite_pattern_at s v)"
proof (induction p u rule: finite_pattern_at.induct)
  case (2 p q d w) then show ?case by (cases d) simp_all
qed simp_all

lemma finite_pattern_at_variables:
  "finite_pattern_at p w = Some s \<Longrightarrow> fset (finite_pattern_variables s) \<subseteq> fset (finite_pattern_variables p)"
proof (induction p w rule: finite_pattern_at.induct)
  case (2 p q d w) then show ?case by (cases d) auto
qed (auto split: if_splits)

lemma finite_pattern_at_variable_member:
  "finite_pattern_at p w = Some (Finite_Variable a) \<Longrightarrow> a |\<in>| finite_pattern_variables p"
  using finite_pattern_at_variables[of p w "Finite_Variable a"] by auto

lemma finite_pattern_variable_position:
  "a |\<in>| finite_pattern_variables p \<Longrightarrow> \<exists>w. finite_pattern_at p w = Some (Finite_Variable a)"
proof (induction p)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases "a |\<in>| finite_pattern_variables p")
    case True
    then obtain w where "finite_pattern_at p w = Some (Finite_Variable a)" using Finite_Pattern_Pair.IH(1) by blast
    then have "finite_pattern_at (Finite_Pattern_Pair p q) (False # w) = Some (Finite_Variable a)" by simp
    then show ?thesis by blast
  next
    case False
    then have "a |\<in>| finite_pattern_variables q" using Finite_Pattern_Pair.prems by simp
    then obtain w where "finite_pattern_at q w = Some (Finite_Variable a)" using Finite_Pattern_Pair.IH(2) by blast
    then have "finite_pattern_at (Finite_Pattern_Pair p q) (True # w) = Some (Finite_Variable a)" by simp
    then show ?thesis by blast
  qed
qed (auto intro!: exI[of _ "[]"])

lemma finite_pattern_at_substitute:
  "finite_pattern_at p w = Some s \<Longrightarrow>
    finite_pattern_at (finite_pattern_substitute \<theta> p) w = Some (finite_pattern_substitute \<theta> s)"
proof (induction p w rule: finite_pattern_at.induct)
  case (2 p q d w) then show ?case by (cases d) simp_all
qed (auto split: if_splits)

lemma finite_pattern_substitute_variables:
  "fset (finite_pattern_variables (finite_pattern_substitute s p)) =
    (\<Union>b\<in>fset (finite_pattern_variables p). fset (finite_pattern_variables (s b)))"
  by (induction p) auto

section \<open>The region of a pattern and its repeated positions\<close>

text \<open>
  The region of a pattern is the set of its positions where it has a constructor or a literal: closed under
  prefixes, since a constructor stands at every position above another. A position where a variable stands
  that stands at another position too is repeated; a pattern is linear when it has no repeated position, no
  variable at two of its positions. What a pattern reads of another it is unified with is read at its region
  and, below a repeated position, the whole subterm there.
\<close>

fun finite_pattern_region :: "'a finite_term_pattern \<Rightarrow> bool list fset" where
  "finite_pattern_region (Finite_Variable a) = {||}"
| "finite_pattern_region (Finite_Pattern_Target t) = {|[]|}"
| "finite_pattern_region (Finite_Pattern_Payload v) = {|[]|}"
| "finite_pattern_region (Finite_Pattern_Pair p q) =
    finsert [] (Cons False |`| finite_pattern_region p |\<union>| Cons True |`| finite_pattern_region q)"

lemma finite_pattern_region_root: "[] |\<in>| finite_pattern_region (Finite_Pattern_Pair p q)"
  by simp

lemma finite_pattern_region_pair:
  "d # w |\<in>| finite_pattern_region (Finite_Pattern_Pair p q) \<longleftrightarrow>
    w |\<in>| finite_pattern_region (if d then q else p)"
  by (cases d) (auto simp: fimage.rep_eq)

lemma finite_pattern_region_member:
  "w |\<in>| finite_pattern_region p \<longleftrightarrow>
    (\<exists>s. finite_pattern_at p w = Some s \<and> (\<forall>a. s \<noteq> Finite_Variable a))"
proof (induction p arbitrary: w)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases w)
    case Nil then show ?thesis by simp
  next
    case (Cons d w')
    have "w |\<in>| finite_pattern_region (Finite_Pattern_Pair p q) \<longleftrightarrow>
        w' |\<in>| finite_pattern_region (if d then q else p)"
      unfolding Cons by (rule finite_pattern_region_pair)
    also have "\<dots> \<longleftrightarrow> (\<exists>s. finite_pattern_at (if d then q else p) w' = Some s \<and> (\<forall>a. s \<noteq> Finite_Variable a))"
      using Finite_Pattern_Pair.IH by (cases d) simp_all
    finally show ?thesis using Cons by simp
  qed
qed auto

lemma finite_pattern_region_below:
  assumes "finite_pattern_at p (u @ d # v) = Some s"
  shows "u |\<in>| finite_pattern_region p"
proof -
  obtain s' where s': "finite_pattern_at p u = Some s'" "finite_pattern_at s' (d # v) = Some s"
    using assms by (auto simp: finite_pattern_at_append split: option.splits)
  then have "\<forall>a. s' \<noteq> Finite_Variable a" by auto
  then show ?thesis using s'(1) by (auto simp: finite_pattern_region_member)
qed

lemma finite_pattern_region_prefix:
  assumes "u @ v |\<in>| finite_pattern_region p"
  shows "u |\<in>| finite_pattern_region p"
proof (cases v)
  case Nil then show ?thesis using assms by simp
next
  case (Cons d v')
  obtain s where "finite_pattern_at p (u @ d # v') = Some s"
    using assms Cons by (auto simp: finite_pattern_region_member)
  then show ?thesis by (rule finite_pattern_region_below)
qed

text \<open>The positions at which each variable stands.\<close>

fun finite_pattern_positions :: "'a finite_term_pattern \<Rightarrow> (bool list \<times> 'a) fset" where
  "finite_pattern_positions (Finite_Variable a) = {|([],a)|}"
| "finite_pattern_positions (Finite_Pattern_Target t) = {||}"
| "finite_pattern_positions (Finite_Pattern_Payload v) = {||}"
| "finite_pattern_positions (Finite_Pattern_Pair p q) =
    (\<lambda>x. (False # fst x, snd x)) |`| finite_pattern_positions p |\<union>|
      (\<lambda>x. (True # fst x, snd x)) |`| finite_pattern_positions q"

lemma finite_pattern_positions_member:
  "(w,a) |\<in>| finite_pattern_positions p \<longleftrightarrow> finite_pattern_at p w = Some (Finite_Variable a)"
proof (induction p arbitrary: w)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases w)
    case Nil then show ?thesis by (auto simp: fimage.rep_eq)
  next
    case (Cons d w')
    have "(d # w', a) |\<in>| finite_pattern_positions (Finite_Pattern_Pair p q) \<longleftrightarrow>
        (w', a) |\<in>| finite_pattern_positions (if d then q else p)"
      by (cases d) (force simp: fimage.rep_eq)+
    then show ?thesis using Cons Finite_Pattern_Pair.IH by (cases d) simp_all
  qed
qed auto

definition finite_pattern_repeated :: "'a finite_term_pattern \<Rightarrow> bool list fset" where
  "finite_pattern_repeated p = fst |`| ffilter (\<lambda>x. \<exists>y. y |\<in>| finite_pattern_positions p \<and>
    snd y = snd x \<and> fst y \<noteq> fst x) (finite_pattern_positions p)"

lemma finite_pattern_repeated_member:
  "w |\<in>| finite_pattern_repeated p \<longleftrightarrow>
    (\<exists>a w'. finite_pattern_at p w = Some (Finite_Variable a) \<and>
      finite_pattern_at p w' = Some (Finite_Variable a) \<and> w' \<noteq> w)"
proof
  assume "w |\<in>| finite_pattern_repeated p"
  then obtain x y where x: "x |\<in>| finite_pattern_positions p" "w = fst x"
      and y: "y |\<in>| finite_pattern_positions p" "snd y = snd x" "fst y \<noteq> fst x"
    by (auto simp: finite_pattern_repeated_def fimage.rep_eq)
  have "finite_pattern_at p (fst x) = Some (Finite_Variable (snd x))"
    using x(1) finite_pattern_positions_member[of "fst x" "snd x" p] by simp
  moreover have "finite_pattern_at p (fst y) = Some (Finite_Variable (snd y))"
    using y(1) finite_pattern_positions_member[of "fst y" "snd y" p] by simp
  then have "finite_pattern_at p (fst y) = Some (Finite_Variable (snd x))" using y(2) by simp
  ultimately show "\<exists>a w'. finite_pattern_at p w = Some (Finite_Variable a) \<and>
      finite_pattern_at p w' = Some (Finite_Variable a) \<and> w' \<noteq> w"
    using x(2) y(3) by blast
next
  assume "\<exists>a w'. finite_pattern_at p w = Some (Finite_Variable a) \<and>
      finite_pattern_at p w' = Some (Finite_Variable a) \<and> w' \<noteq> w"
  then obtain a w' where a: "finite_pattern_at p w = Some (Finite_Variable a)"
      "finite_pattern_at p w' = Some (Finite_Variable a)" "w' \<noteq> w" by blast
  then have pw: "(w,a) |\<in>| finite_pattern_positions p" and pw': "(w',a) |\<in>| finite_pattern_positions p"
    by (simp_all add: finite_pattern_positions_member)
  have filt: "(w,a) |\<in>| ffilter (\<lambda>x. \<exists>y. y |\<in>| finite_pattern_positions p \<and>
      snd y = snd x \<and> fst y \<noteq> fst x) (finite_pattern_positions p)"
    by (simp add: pw) (rule exI[of _ w'], simp add: pw' a(3))
  show "w |\<in>| finite_pattern_repeated p"
    unfolding finite_pattern_repeated_def fimage.rep_eq
    by (rule image_eqI[where x="(w,a)"], simp, rule filt)
qed

definition finite_pattern_linear :: "'a finite_term_pattern \<Rightarrow> bool" where
  "finite_pattern_linear p \<longleftrightarrow> finite_pattern_repeated p = {||}"

lemma finite_pattern_linear_positions:
  "finite_pattern_linear p \<longleftrightarrow> (\<forall>w w' a. finite_pattern_at p w = Some (Finite_Variable a) \<longrightarrow>
    finite_pattern_at p w' = Some (Finite_Variable a) \<longrightarrow> w = w')"
proof -
  have "finite_pattern_repeated p = {||} \<longleftrightarrow> (\<forall>w. w |\<notin>| finite_pattern_repeated p)"
    by (auto intro: fset_eqI)
  then show ?thesis unfolding finite_pattern_linear_def finite_pattern_repeated_member by blast
qed

lemma finite_pattern_linear_repeated: "finite_pattern_linear p \<Longrightarrow> finite_pattern_repeated p = {||}"
  by (simp add: finite_pattern_linear_def)

subsection \<open>A renaming of variables keeps the region and the repetitions\<close>

lemma finite_pattern_at_map:
  "finite_pattern_at (map_finite_term_pattern f p) w =
    map_option (map_finite_term_pattern f) (finite_pattern_at p w)"
proof (induction p w rule: finite_pattern_at.induct)
  case (2 p q d w) then show ?case by (cases d) simp_all
qed simp_all

lemma map_finite_term_pattern_variable_iff:
  "map_finite_term_pattern f s = Finite_Variable b \<longleftrightarrow> (\<exists>a. s = Finite_Variable a \<and> b = f a)"
  by (cases s) auto

lemma finite_pattern_at_map_variable:
  "finite_pattern_at (map_finite_term_pattern f p) w = Some (Finite_Variable b) \<longleftrightarrow>
    (\<exists>a. finite_pattern_at p w = Some (Finite_Variable a) \<and> b = f a)"
  by (auto simp: finite_pattern_at_map map_finite_term_pattern_variable_iff)

lemma finite_pattern_region_map [simp]:
  "finite_pattern_region (map_finite_term_pattern f p) = finite_pattern_region p"
  by (induction p) simp_all

lemma finite_pattern_repeated_map:
  assumes "inj f"
  shows "finite_pattern_repeated (map_finite_term_pattern f p) = finite_pattern_repeated p"
proof (rule fset_eqI)
  fix w
  show "w |\<in>| finite_pattern_repeated (map_finite_term_pattern f p) \<longleftrightarrow> w |\<in>| finite_pattern_repeated p"
    unfolding finite_pattern_repeated_member finite_pattern_at_map_variable
    by (fastforce dest: injD[OF assms])
qed

lemma finite_pattern_linear_map:
  assumes "inj f"
  shows "finite_pattern_linear (map_finite_term_pattern f p) \<longleftrightarrow> finite_pattern_linear p"
  by (simp add: finite_pattern_linear_def finite_pattern_repeated_map[OF assms])

lemma finite_rename_apart_region [simp]:
  "finite_pattern_region (finite_rename_apart w p) = finite_pattern_region p"
  by (simp add: finite_rename_apart_def)

lemma finite_rename_apart_repeated [simp]:
  "finite_pattern_repeated (finite_rename_apart w p) = finite_pattern_repeated p"
  using finite_pattern_repeated_map[of "Pair w" p] by (simp add: finite_rename_apart_def inj_def)

lemma finite_rename_apart_linear [simp]:
  "finite_pattern_linear (finite_rename_apart w p) \<longleftrightarrow> finite_pattern_linear p"
  by (simp add: finite_pattern_linear_def)

section \<open>The variables of a pattern at a set of positions\<close>

text \<open>
  The variables standing at positions of a set, and the variables of the subterms at positions of a set,
  among the pattern's variables. What a reader with region @{term R} and repeated positions @{term D} reads of
  a pattern is the variables at @{term R} and the variables under @{term D}.
\<close>

definition finite_pattern_variables_at :: "'a finite_term_pattern \<Rightarrow> bool list fset \<Rightarrow> 'a fset" where
  "finite_pattern_variables_at g W = ffilter (\<lambda>b. \<exists>w. w |\<in>| W \<and>
    finite_pattern_at g w = Some (Finite_Variable b)) (finite_pattern_variables g)"

definition finite_pattern_variables_under :: "'a finite_term_pattern \<Rightarrow> bool list fset \<Rightarrow> 'a fset" where
  "finite_pattern_variables_under g W = ffilter (\<lambda>b. \<exists>w. w |\<in>| W \<and>
    (\<exists>s. finite_pattern_at g w = Some s \<and> b |\<in>| finite_pattern_variables s)) (finite_pattern_variables g)"

definition finite_read_variables :: "bool list fset \<Rightarrow> bool list fset \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'a fset" where
  "finite_read_variables R D g = finite_pattern_variables_at g R |\<union>| finite_pattern_variables_under g D"

lemma finite_pattern_variables_at_member:
  "b |\<in>| finite_pattern_variables_at g W \<longleftrightarrow>
    (\<exists>w. w |\<in>| W \<and> finite_pattern_at g w = Some (Finite_Variable b))"
  by (auto simp: finite_pattern_variables_at_def dest: finite_pattern_at_variable_member)

lemma finite_pattern_variables_under_member:
  "b |\<in>| finite_pattern_variables_under g W \<longleftrightarrow>
    (\<exists>w. w |\<in>| W \<and> (\<exists>s. finite_pattern_at g w = Some s \<and> b |\<in>| finite_pattern_variables s))"
  by (auto simp: finite_pattern_variables_under_def dest: finite_pattern_at_variables)

lemma finite_pattern_variables_at_subset:
  "fset (finite_pattern_variables_at g W) \<subseteq> fset (finite_pattern_variables g)"
  by (auto simp: finite_pattern_variables_at_def)

lemma finite_pattern_variables_under_subset:
  "fset (finite_pattern_variables_under g W) \<subseteq> fset (finite_pattern_variables g)"
  by (auto simp: finite_pattern_variables_under_def)

lemma finite_pattern_variables_under_empty [simp]: "finite_pattern_variables_under g {||} = {||}"
  by (rule fset_eqI) (simp add: finite_pattern_variables_under_member)

lemma finite_read_variables_member:
  "b |\<in>| finite_read_variables R D g \<longleftrightarrow>
    (\<exists>w. w |\<in>| R \<and> finite_pattern_at g w = Some (Finite_Variable b)) \<or>
    (\<exists>w. w |\<in>| D \<and> (\<exists>s. finite_pattern_at g w = Some s \<and> b |\<in>| finite_pattern_variables s))"
  by (simp add: finite_read_variables_def finite_pattern_variables_at_member finite_pattern_variables_under_member)

lemma finite_read_variables_mono:
  assumes "b |\<in>| finite_read_variables R D g" "fset R \<subseteq> fset R'" "fset D \<subseteq> fset D'"
  shows "b |\<in>| finite_read_variables R' D' g"
  using assms by (auto simp: finite_read_variables_member)

lemma finite_read_variables_linear:
  "finite_read_variables R {||} g = finite_pattern_variables_at g R"
  by (simp add: finite_read_variables_def)

section \<open>Matching reads a pattern at the reader's region and under its repeated positions\<close>

text \<open>
  A pattern covers another where they agree on the reader's constructors and literals, the other arbitrary
  below the reader's variables. A pattern has an instance equal to a pattern exactly when it covers it and the
  subterms at the positions of each of its variables are equal.
\<close>

fun finite_pattern_covers :: "'a finite_term_pattern \<Rightarrow> 'b finite_term_pattern \<Rightarrow> bool" where
  "finite_pattern_covers (Finite_Variable a) t \<longleftrightarrow> True"
| "finite_pattern_covers (Finite_Pattern_Target x) t \<longleftrightarrow> t = Finite_Pattern_Target x"
| "finite_pattern_covers (Finite_Pattern_Payload v) t \<longleftrightarrow> t = Finite_Pattern_Payload v"
| "finite_pattern_covers (Finite_Pattern_Pair p q) t \<longleftrightarrow>
    (case t of Finite_Pattern_Pair t1 t2 \<Rightarrow> finite_pattern_covers p t1 \<and> finite_pattern_covers q t2 | _ \<Rightarrow> False)"

lemma finite_pattern_covers_substitute_self: "finite_pattern_covers p (finite_pattern_substitute \<theta> p)"
  by (induction p) simp_all

lemma finite_pattern_covers_at:
  assumes "finite_pattern_covers p t" "finite_pattern_at p w = Some s"
  shows "\<exists>s'. finite_pattern_at t w = Some s'"
  using assms
proof (induction p arbitrary: t w s)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases w)
    case Nil then show ?thesis by simp
  next
    case (Cons d w')
    obtain t1 t2 where t: "t = Finite_Pattern_Pair t1 t2" "finite_pattern_covers p t1" "finite_pattern_covers q t2"
      using Finite_Pattern_Pair.prems(1) by (cases t) auto
    show ?thesis using Finite_Pattern_Pair.IH Finite_Pattern_Pair.prems(2) t Cons by (cases d) auto
  qed
qed (auto split: if_splits)

lemma finite_pattern_covers_instance:
  assumes "finite_pattern_covers p t"
    and "\<And>a w. finite_pattern_at p w = Some (Finite_Variable a) \<Longrightarrow> finite_pattern_at t w = Some (\<theta> a)"
  shows "finite_pattern_substitute \<theta> p = t"
  using assms
proof (induction p arbitrary: t)
  case (Finite_Variable a)
  show ?case using Finite_Variable.prems(2)[where a=a and w="[]"] by simp
next
  case (Finite_Pattern_Pair p q)
  obtain t1 t2 where t: "t = Finite_Pattern_Pair t1 t2" "finite_pattern_covers p t1" "finite_pattern_covers q t2"
    using Finite_Pattern_Pair.prems(1) by (cases t) auto
  have p: "finite_pattern_substitute \<theta> p = t1"
  proof (rule Finite_Pattern_Pair.IH(1)[OF t(2)])
    fix a w assume "finite_pattern_at p w = Some (Finite_Variable a)"
    then show "finite_pattern_at t1 w = Some (\<theta> a)"
      using Finite_Pattern_Pair.prems(2)[where a=a and w="False # w"] t(1) by simp
  qed
  have q: "finite_pattern_substitute \<theta> q = t2"
  proof (rule Finite_Pattern_Pair.IH(2)[OF t(3)])
    fix a w assume "finite_pattern_at q w = Some (Finite_Variable a)"
    then show "finite_pattern_at t2 w = Some (\<theta> a)"
      using Finite_Pattern_Pair.prems(2)[where a=a and w="True # w"] t(1) by simp
  qed
  show ?case using p q t(1) by simp
qed auto

theorem finite_pattern_matches:
  "(\<exists>\<theta>. finite_pattern_substitute \<theta> p = t) \<longleftrightarrow> finite_pattern_covers p t \<and>
    (\<forall>w w' a. finite_pattern_at p w = Some (Finite_Variable a) \<longrightarrow>
      finite_pattern_at p w' = Some (Finite_Variable a) \<longrightarrow> finite_pattern_at t w = finite_pattern_at t w')"
proof
  assume "\<exists>\<theta>. finite_pattern_substitute \<theta> p = t"
  then obtain \<theta> where \<theta>: "finite_pattern_substitute \<theta> p = t" by blast
  have "finite_pattern_covers p t" using finite_pattern_covers_substitute_self[of p \<theta>] \<theta> by simp
  moreover have "finite_pattern_at t w = finite_pattern_at t w'"
    if "finite_pattern_at p w = Some (Finite_Variable a)" "finite_pattern_at p w' = Some (Finite_Variable a)"
    for w w' a
    using finite_pattern_at_substitute[OF that(1), of \<theta>] finite_pattern_at_substitute[OF that(2), of \<theta>] \<theta>
    by simp
  ultimately show "finite_pattern_covers p t \<and> (\<forall>w w' a. finite_pattern_at p w = Some (Finite_Variable a) \<longrightarrow>
      finite_pattern_at p w' = Some (Finite_Variable a) \<longrightarrow> finite_pattern_at t w = finite_pattern_at t w')"
    by blast
next
  assume r: "finite_pattern_covers p t \<and> (\<forall>w w' a. finite_pattern_at p w = Some (Finite_Variable a) \<longrightarrow>
      finite_pattern_at p w' = Some (Finite_Variable a) \<longrightarrow> finite_pattern_at t w = finite_pattern_at t w')"
  define \<theta> where "\<theta> a = the (finite_pattern_at t (SOME w. finite_pattern_at p w = Some (Finite_Variable a)))" for a
  have "finite_pattern_substitute \<theta> p = t"
  proof (rule finite_pattern_covers_instance)
    show "finite_pattern_covers p t" using r by blast
    fix a w assume w: "finite_pattern_at p w = Some (Finite_Variable a)"
    have w0: "finite_pattern_at p (SOME w. finite_pattern_at p w = Some (Finite_Variable a)) = Some (Finite_Variable a)"
      using w by (rule someI)
    obtain s' where s': "finite_pattern_at t w = Some s'"
      using finite_pattern_covers_at[OF _ w] r by blast
    have "finite_pattern_at t w = finite_pattern_at t (SOME w. finite_pattern_at p w = Some (Finite_Variable a))"
      using r w w0 by blast
    then show "finite_pattern_at t w = Some (\<theta> a)" using s' unfolding \<theta>_def by (metis option.sel)
  qed
  then show "\<exists>\<theta>. finite_pattern_substitute \<theta> p = t" by blast
qed

text \<open>
  A substitution binding no variable that stands at a position of the reader's region, nor any variable
  under its repeated positions, changes neither whether the reader covers an instance nor the subterms the
  reader's repeated variables compare.
\<close>

lemma finite_pattern_at_fixed:
  assumes "\<And>u v b. w = u @ v \<Longrightarrow> finite_pattern_at g u = Some (Finite_Variable b) \<Longrightarrow> \<sigma> b = Finite_Variable b"
    and "\<And>s b. finite_pattern_at g w = Some s \<Longrightarrow> b |\<in>| finite_pattern_variables s \<Longrightarrow> \<sigma> b = Finite_Variable b"
  shows "finite_pattern_at (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g)) w =
    finite_pattern_at (finite_pattern_substitute \<rho> g) w"
  using assms
proof (induction g arbitrary: w)
  case (Finite_Variable b)
  have "\<sigma> b = Finite_Variable b" using Finite_Variable.prems(1)[of "[]" w b] by simp
  then show ?case by simp
next
  case (Finite_Pattern_Pair g1 g2)
  note IH = Finite_Pattern_Pair.IH and prems = Finite_Pattern_Pair.prems
  show ?case
  proof (cases w)
    case Nil
    have "finite_pattern_substitute \<sigma> (Finite_Pattern_Pair g1 g2) =
        finite_pattern_substitute Finite_Variable (Finite_Pattern_Pair g1 g2)"
      by (rule finite_pattern_substitute_cong) (use prems(2)[of "Finite_Pattern_Pair g1 g2"] Nil in simp)
    then show ?thesis by simp
  next
    case (Cons d w')
    have g1: "finite_pattern_at (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g1)) w' =
        finite_pattern_at (finite_pattern_substitute \<rho> g1) w'" if "\<not> d"
    proof (rule IH(1))
      fix u v b assume "w' = u @ v" "finite_pattern_at g1 u = Some (Finite_Variable b)"
      then show "\<sigma> b = Finite_Variable b" using prems(1)[of "False # u" v b] Cons that by simp
    next
      fix s b assume "finite_pattern_at g1 w' = Some s" "b |\<in>| finite_pattern_variables s"
      then show "\<sigma> b = Finite_Variable b" using prems(2)[of s b] Cons that by simp
    qed
    have g2: "finite_pattern_at (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g2)) w' =
        finite_pattern_at (finite_pattern_substitute \<rho> g2) w'" if d
    proof (rule IH(2))
      fix u v b assume "w' = u @ v" "finite_pattern_at g2 u = Some (Finite_Variable b)"
      then show "\<sigma> b = Finite_Variable b" using prems(1)[of "True # u" v b] Cons that by simp
    next
      fix s b assume "finite_pattern_at g2 w' = Some s" "b |\<in>| finite_pattern_variables s"
      then show "\<sigma> b = Finite_Variable b" using prems(2)[of s b] Cons that by simp
    qed
    show ?thesis using Cons g1 g2 by (cases d) simp_all
  qed
qed simp_all

lemma finite_pattern_covers_fixed:
  assumes "\<And>w b. w |\<in>| finite_pattern_region p \<Longrightarrow> finite_pattern_at g w = Some (Finite_Variable b) \<Longrightarrow>
      \<sigma> b = Finite_Variable b"
  shows "finite_pattern_covers p (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g)) \<longleftrightarrow>
    finite_pattern_covers p (finite_pattern_substitute \<rho> g)"
  using assms
proof (induction p arbitrary: g)
  case (Finite_Variable a) then show ?case by simp
next
  case (Finite_Pattern_Target x)
  show ?case
  proof (cases g)
    case (Finite_Variable b)
    have "\<sigma> b = Finite_Variable b" using Finite_Pattern_Target.prems[of "[]" b] Finite_Variable by simp
    then show ?thesis using Finite_Variable by simp
  qed simp_all
next
  case (Finite_Pattern_Payload v)
  show ?case
  proof (cases g)
    case (Finite_Variable b)
    have "\<sigma> b = Finite_Variable b" using Finite_Pattern_Payload.prems[of "[]" b] Finite_Variable by simp
    then show ?thesis using Finite_Variable by simp
  qed simp_all
next
  case (Finite_Pattern_Pair p q)
  note IH = Finite_Pattern_Pair.IH and prems = Finite_Pattern_Pair.prems
  show ?case
  proof (cases g)
    case (Finite_Variable b)
    have "\<sigma> b = Finite_Variable b" using prems[of "[]" b] Finite_Variable by simp
    then show ?thesis using Finite_Variable by simp
  next
    case (Finite_Pattern_Pair g1 g2)
    have "finite_pattern_covers p (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g1)) \<longleftrightarrow>
        finite_pattern_covers p (finite_pattern_substitute \<rho> g1)"
    proof (rule IH(1))
      fix w b assume "w |\<in>| finite_pattern_region p" "finite_pattern_at g1 w = Some (Finite_Variable b)"
      then show "\<sigma> b = Finite_Variable b"
        using prems[of "False # w" b] Finite_Pattern_Pair by (simp add: finite_pattern_region_pair)
    qed
    moreover have "finite_pattern_covers q (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g2)) \<longleftrightarrow>
        finite_pattern_covers q (finite_pattern_substitute \<rho> g2)"
    proof (rule IH(2))
      fix w b assume "w |\<in>| finite_pattern_region q" "finite_pattern_at g2 w = Some (Finite_Variable b)"
      then show "\<sigma> b = Finite_Variable b"
        using prems[of "True # w" b] Finite_Pattern_Pair by (simp add: finite_pattern_region_pair)
    qed
    ultimately show ?thesis using Finite_Pattern_Pair by simp
  qed simp_all
qed

theorem finite_pattern_matches_fixed:
  assumes "\<And>b. b |\<in>| finite_read_variables (finite_pattern_region p) (finite_pattern_repeated p) g \<Longrightarrow>
      \<sigma> b = Finite_Variable b"
  shows "(\<exists>\<theta>. finite_pattern_substitute \<theta> p = finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g)) \<longleftrightarrow>
    (\<exists>\<theta>. finite_pattern_substitute \<theta> p = finite_pattern_substitute \<rho> g)"
proof -
  have region: "\<sigma> b = Finite_Variable b"
    if "w |\<in>| finite_pattern_region p" "finite_pattern_at g w = Some (Finite_Variable b)" for w b
    using assms that by (auto simp: finite_read_variables_member)
  have deep: "finite_pattern_at (finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g)) w =
      finite_pattern_at (finite_pattern_substitute \<rho> g) w" if w: "w |\<in>| finite_pattern_repeated p" for w
  proof (rule finite_pattern_at_fixed)
    fix u v b assume uv: "w = u @ v" "finite_pattern_at g u = Some (Finite_Variable b)"
    show "\<sigma> b = Finite_Variable b"
    proof (cases v)
      case Nil
      then show ?thesis using w uv by (intro assms) (auto simp: finite_read_variables_member)
    next
      case (Cons d v')
      obtain a where "finite_pattern_at p w = Some (Finite_Variable a)"
        using w by (auto simp: finite_pattern_repeated_member)
      then have "u |\<in>| finite_pattern_region p"
        using uv(1) Cons by (auto intro: finite_pattern_region_below)
      then show ?thesis using region uv(2) by blast
    qed
  next
    fix s b assume "finite_pattern_at g w = Some s" "b |\<in>| finite_pattern_variables s"
    then show "\<sigma> b = Finite_Variable b" using w by (intro assms) (auto simp: finite_read_variables_member)
  qed
  let ?T1 = "finite_pattern_substitute \<rho> (finite_pattern_substitute \<sigma> g)"
  let ?T2 = "finite_pattern_substitute \<rho> g"
  have pairs: "finite_pattern_at ?T1 w = finite_pattern_at ?T1 w' \<longleftrightarrow> finite_pattern_at ?T2 w = finite_pattern_at ?T2 w'"
    if "finite_pattern_at p w = Some (Finite_Variable a)" "finite_pattern_at p w' = Some (Finite_Variable a)"
    for w w' a
  proof (cases "w = w'")
    case False
    have "w |\<in>| finite_pattern_repeated p"
      unfolding finite_pattern_repeated_member using that not_sym[OF False] by blast
    moreover have "w' |\<in>| finite_pattern_repeated p"
      unfolding finite_pattern_repeated_member using that False by blast
    ultimately show ?thesis using deep by simp
  qed simp
  have covers: "finite_pattern_covers p ?T1 \<longleftrightarrow> finite_pattern_covers p ?T2"
    by (rule finite_pattern_covers_fixed) (rule region)
  show ?thesis unfolding finite_pattern_matches using covers pairs by blast
qed

section \<open>Unification is kept across every binding outside the region\<close>

text \<open>
  Two patterns with disjoint variables, fresh for a third, unify jointly with it exactly when some instance of
  the third is an instance of each: the variables of the two are bound independently.
\<close>

lemma finite_unifies_matches:
  fixes i h g :: "'a finite_term_pattern"
  assumes apart: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables h) = {}"
    and fresh: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables g) = {}"
      "fset (finite_pattern_variables h) \<inter> fset (finite_pattern_variables g) = {}"
  shows "(\<exists>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. finite_unifies \<theta> [(i,g),(h,g)]) \<longleftrightarrow>
    (\<exists>\<rho>::'a \<Rightarrow> 'b finite_term_pattern. (\<exists>\<theta>. finite_pattern_substitute \<theta> i = finite_pattern_substitute \<rho> g) \<and>
      (\<exists>\<theta>. finite_pattern_substitute \<theta> h = finite_pattern_substitute \<rho> g))"
proof
  assume "\<exists>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. finite_unifies \<theta> [(i,g),(h,g)]"
  then obtain \<theta> :: "'a \<Rightarrow> 'b finite_term_pattern" where
    "finite_pattern_substitute \<theta> i = finite_pattern_substitute \<theta> g"
    "finite_pattern_substitute \<theta> h = finite_pattern_substitute \<theta> g" by auto
  then show "\<exists>\<rho>::'a \<Rightarrow> 'b finite_term_pattern. (\<exists>\<theta>. finite_pattern_substitute \<theta> i = finite_pattern_substitute \<rho> g) \<and>
      (\<exists>\<theta>. finite_pattern_substitute \<theta> h = finite_pattern_substitute \<rho> g)" by blast
next
  assume "\<exists>\<rho>::'a \<Rightarrow> 'b finite_term_pattern. (\<exists>\<theta>. finite_pattern_substitute \<theta> i = finite_pattern_substitute \<rho> g) \<and>
      (\<exists>\<theta>. finite_pattern_substitute \<theta> h = finite_pattern_substitute \<rho> g)"
  then obtain \<rho> \<theta>i \<theta>h :: "'a \<Rightarrow> 'b finite_term_pattern" where
    si: "finite_pattern_substitute \<theta>i i = finite_pattern_substitute \<rho> g" and
    sh: "finite_pattern_substitute \<theta>h h = finite_pattern_substitute \<rho> g" by blast
  define \<theta> where "\<theta> a = (if a |\<in>| finite_pattern_variables i then \<theta>i a
    else if a |\<in>| finite_pattern_variables h then \<theta>h a else \<rho> a)" for a
  have "finite_pattern_substitute \<theta> i = finite_pattern_substitute \<theta>i i"
    by (rule finite_pattern_substitute_cong) (simp add: \<theta>_def)
  moreover have "finite_pattern_substitute \<theta> h = finite_pattern_substitute \<theta>h h"
    by (rule finite_pattern_substitute_cong) (use apart in \<open>auto simp: \<theta>_def disjoint_iff\<close>)
  moreover have "finite_pattern_substitute \<theta> g = finite_pattern_substitute \<rho> g"
    by (rule finite_pattern_substitute_cong) (use fresh in \<open>auto simp: \<theta>_def disjoint_iff\<close>)
  ultimately have "finite_unifies \<theta> [(i,g),(h,g)]" using si sh by simp
  then show "\<exists>\<theta>::'a \<Rightarrow> 'b finite_term_pattern. finite_unifies \<theta> [(i,g),(h,g)]" by blast
qed

theorem finite_unify_pairs_region:
  fixes i h g :: "'a finite_term_pattern" and \<sigma> :: "'a \<Rightarrow> 'a finite_term_pattern"
  assumes apart: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables h) = {}"
    and fresh: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables g) = {}"
      "fset (finite_pattern_variables h) \<inter> fset (finite_pattern_variables g) = {}"
    and images: "\<And>b. b |\<in>| finite_pattern_variables g \<Longrightarrow> fset (finite_pattern_variables (\<sigma> b)) \<inter>
      (fset (finite_pattern_variables i) \<union> fset (finite_pattern_variables h)) = {}"
    and outside: "\<And>b. b |\<in>| finite_read_variables (finite_pattern_region i |\<union>| finite_pattern_region h)
      (finite_pattern_repeated i |\<union>| finite_pattern_repeated h) g \<Longrightarrow> \<sigma> b = Finite_Variable b"
  shows "finite_unify_pairs [(i,g),(h,g)] = None \<longleftrightarrow>
    finite_unify_pairs [(i, finite_pattern_substitute \<sigma> g),(h, finite_pattern_substitute \<sigma> g)] = None"
proof -
  let ?g = "finite_pattern_substitute \<sigma> g"
  have fresh': "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables ?g) = {}"
    "fset (finite_pattern_variables h) \<inter> fset (finite_pattern_variables ?g) = {}"
    using images unfolding finite_pattern_substitute_variables by blast+
  have mi: "(\<exists>\<theta>. finite_pattern_substitute \<theta> i = finite_pattern_substitute \<rho> ?g) \<longleftrightarrow>
      (\<exists>\<theta>. finite_pattern_substitute \<theta> i = finite_pattern_substitute \<rho> g)" for \<rho> :: "'a \<Rightarrow> 'a finite_term_pattern"
  proof (rule finite_pattern_matches_fixed)
    fix b assume "b |\<in>| finite_read_variables (finite_pattern_region i) (finite_pattern_repeated i) g"
    then show "\<sigma> b = Finite_Variable b" by (intro outside) (auto simp: finite_read_variables_member)
  qed
  have mh: "(\<exists>\<theta>. finite_pattern_substitute \<theta> h = finite_pattern_substitute \<rho> ?g) \<longleftrightarrow>
      (\<exists>\<theta>. finite_pattern_substitute \<theta> h = finite_pattern_substitute \<rho> g)" for \<rho> :: "'a \<Rightarrow> 'a finite_term_pattern"
  proof (rule finite_pattern_matches_fixed)
    fix b assume "b |\<in>| finite_read_variables (finite_pattern_region h) (finite_pattern_repeated h) g"
    then show "\<sigma> b = Finite_Variable b" by (intro outside) (auto simp: finite_read_variables_member)
  qed
  have "(\<exists>\<theta>::'a \<Rightarrow> 'a finite_term_pattern. finite_unifies \<theta> [(i,g),(h,g)]) \<longleftrightarrow>
      (\<exists>\<theta>::'a \<Rightarrow> 'a finite_term_pattern. finite_unifies \<theta> [(i,?g),(h,?g)])"
    by (simp only: finite_unifies_matches[OF apart fresh] finite_unifies_matches[OF apart fresh'] mi mh)
  then show ?thesis
    using finite_unify_pairs_none_iff[where 'b='a, of "[(i,g),(h,g)]"]
      finite_unify_pairs_none_iff[where 'b='a, of "[(i,?g),(h,?g)]"] by blast
qed

corollary finite_unify_pairs_linear_region:
  fixes i h g :: "'a finite_term_pattern" and \<sigma> :: "'a \<Rightarrow> 'a finite_term_pattern"
  assumes linear: "finite_pattern_linear i" "finite_pattern_linear h"
    and apart: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables h) = {}"
    and fresh: "fset (finite_pattern_variables i) \<inter> fset (finite_pattern_variables g) = {}"
      "fset (finite_pattern_variables h) \<inter> fset (finite_pattern_variables g) = {}"
    and images: "\<And>b. b |\<in>| finite_pattern_variables g \<Longrightarrow> fset (finite_pattern_variables (\<sigma> b)) \<inter>
      (fset (finite_pattern_variables i) \<union> fset (finite_pattern_variables h)) = {}"
    and outside: "\<And>b. b |\<in>| finite_pattern_variables_at g (finite_pattern_region i |\<union>| finite_pattern_region h) \<Longrightarrow>
      \<sigma> b = Finite_Variable b"
  shows "finite_unify_pairs [(i,g),(h,g)] = None \<longleftrightarrow>
    finite_unify_pairs [(i, finite_pattern_substitute \<sigma> g),(h, finite_pattern_substitute \<sigma> g)] = None"
proof (rule finite_unify_pairs_region[OF apart fresh images])
  fix b assume "b |\<in>| finite_read_variables (finite_pattern_region i |\<union>| finite_pattern_region h)
      (finite_pattern_repeated i |\<union>| finite_pattern_repeated h) g"
  then show "\<sigma> b = Finite_Variable b"
    using outside by (simp add: finite_pattern_linear_repeated[OF linear(1)] finite_pattern_linear_repeated[OF linear(2)]
      finite_read_variables_linear)
qed

section \<open>The count of a call goal's alternatives is kept across every binding outside its site's region\<close>

text \<open>
  The region of a site is the union of the regions of its interfaces and clause heads, and its repeated
  positions the union of theirs; renaming apart keeps both. A site is linear when its interfaces and clause
  heads are, and then it has no repeated position.
\<close>

definition finite_site_region :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> bool list fset" where
  "finite_site_region P d =
    ffUnion ((\<lambda>x. if fst x = d then finite_pattern_region (snd x) else {||}) |`| finite_system_interfaces P) |\<union>|
    ffUnion ((\<lambda>x. if fst (fst x) = d then finite_pattern_region (finite_schema_conclusion (snd x)) else {||}) |`|
      finite_system_clauses P)"

definition finite_site_repeated :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> bool list fset" where
  "finite_site_repeated P d =
    ffUnion ((\<lambda>x. if fst x = d then finite_pattern_repeated (snd x) else {||}) |`| finite_system_interfaces P) |\<union>|
    ffUnion ((\<lambda>x. if fst (fst x) = d then finite_pattern_repeated (finite_schema_conclusion (snd x)) else {||}) |`|
      finite_system_clauses P)"

definition finite_site_linear :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> bool" where
  "finite_site_linear P d \<longleftrightarrow> (\<forall>i. (d,i) |\<in>| finite_system_interfaces P \<longrightarrow> finite_pattern_linear i) \<and>
    (\<forall>c S. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow> finite_pattern_linear (finite_schema_conclusion S))"

lemma finite_site_region_member:
  "(d,i) |\<in>| finite_system_interfaces P \<Longrightarrow> w |\<in>| finite_pattern_region i \<Longrightarrow> w |\<in>| finite_site_region P d"
  "((d,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> w |\<in>| finite_pattern_region (finite_schema_conclusion S) \<Longrightarrow>
    w |\<in>| finite_site_region P d"
  by (force simp: finite_site_region_def ffUnion.rep_eq fimage.rep_eq)+

lemma finite_site_repeated_member:
  "(d,i) |\<in>| finite_system_interfaces P \<Longrightarrow> w |\<in>| finite_pattern_repeated i \<Longrightarrow> w |\<in>| finite_site_repeated P d"
  "((d,c),S) |\<in>| finite_system_clauses P \<Longrightarrow> w |\<in>| finite_pattern_repeated (finite_schema_conclusion S) \<Longrightarrow>
    w |\<in>| finite_site_repeated P d"
  by (force simp: finite_site_repeated_def ffUnion.rep_eq fimage.rep_eq)+

lemma finite_site_repeated_linear:
  assumes "finite_site_linear P d"
  shows "finite_site_repeated P d = {||}"
proof (rule fset_eqI)
  fix w
  have "w |\<notin>| finite_site_repeated P d"
  proof
    assume "w |\<in>| finite_site_repeated P d"
    then consider (interface) x where "x |\<in>| finite_system_interfaces P" "fst x = d" "w |\<in>| finite_pattern_repeated (snd x)"
      | (clause) x where "x |\<in>| finite_system_clauses P" "fst (fst x) = d"
          "w |\<in>| finite_pattern_repeated (finite_schema_conclusion (snd x))"
      by (auto simp: finite_site_repeated_def ffUnion.rep_eq fimage.rep_eq split: if_splits)
    then show False
    proof cases
      case interface
      then have "(d, snd x) |\<in>| finite_system_interfaces P" by (metis prod.collapse)
      then show False using assms interface(3) by (simp add: finite_site_linear_def finite_pattern_linear_def)
    next
      case clause
      then have "((d, snd (fst x)), snd x) |\<in>| finite_system_clauses P" by (metis prod.collapse)
      then show False using assms clause(3) by (simp add: finite_site_linear_def finite_pattern_linear_def)
    qed
  qed
  then show "w |\<in>| finite_site_repeated P d \<longleftrightarrow> w |\<in>| {||}" by simp
qed

text \<open>
  An alternative of a call goal is an interface and a clause of its site whose renamed patterns unify with
  the goal, with their unifier; the unifier is the one the pair determines.
\<close>

lemma finite_call_alternative_member:
  "(i,c,S,u) |\<in>| finite_call_alternative_set P q d p \<longleftrightarrow>
    (d,i) |\<in>| finite_system_interfaces P \<and> ((d,c),S) |\<in>| finite_system_clauses P \<and>
    finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
proof
  assume "(i,c,S,u) |\<in>| finite_call_alternative_set P q d p"
  then show "(d,i) |\<in>| finite_system_interfaces P \<and> ((d,c),S) |\<in>| finite_system_clauses P \<and>
      finite_unify_pairs [(finite_rename_apart (q,False) i,p),
        (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
    unfolding finite_call_alternative_set_def
    by (auto simp: ffUnion.rep_eq fimage.rep_eq Bex_def split_paired_Ex split: option.splits if_splits)
next
  assume "(d,i) |\<in>| finite_system_interfaces P \<and> ((d,c),S) |\<in>| finite_system_clauses P \<and>
      finite_unify_pairs [(finite_rename_apart (q,False) i,p),
        (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] = Some u"
  then show "(i,c,S,u) |\<in>| finite_call_alternative_set P q d p"
    unfolding finite_call_alternative_set_def
    by (auto simp: ffUnion.rep_eq fimage.rep_eq Bex_def split_paired_Ex intro!: exI[of _ i] exI[of _ c] exI[of _ S])
qed

lemma finite_call_alternative_exists:
  "(\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d p) \<longleftrightarrow>
    (d,i) |\<in>| finite_system_interfaces P \<and> ((d,c),S) |\<in>| finite_system_clauses P \<and>
    finite_unify_pairs [(finite_rename_apart (q,False) i,p),
      (finite_rename_apart (q,True) (finite_schema_conclusion S),p)] \<noteq> None"
  by (auto simp: finite_call_alternative_member)

definition finite_alternative_key :: "'p \<times> 'c \<times> 'S \<times> 'u \<Rightarrow> 'p \<times> 'c \<times> 'S" where
  "finite_alternative_key x = (fst x, fst (snd x), fst (snd (snd x)))"

lemma finite_call_alternative_keys:
  "(i,c,S) \<in> finite_alternative_key ` fset (finite_call_alternative_set P q d p) \<longleftrightarrow>
    (\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d p)"
proof
  assume "(i,c,S) \<in> finite_alternative_key ` fset (finite_call_alternative_set P q d p)"
  then obtain x where x: "x |\<in>| finite_call_alternative_set P q d p" "(i,c,S) = finite_alternative_key x" by blast
  obtain i' c' S' u where "x = (i',c',S',u)" by (rule prod_cases4)
  then show "\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d p"
    using x by (auto simp: finite_alternative_key_def)
next
  assume "\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d p"
  then obtain u where "(i,c,S,u) |\<in>| finite_call_alternative_set P q d p" by blast
  then show "(i,c,S) \<in> finite_alternative_key ` fset (finite_call_alternative_set P q d p)"
    by (rule rev_image_eqI) (simp add: finite_alternative_key_def)
qed

lemma finite_call_alternative_key_inj:
  assumes "x |\<in>| finite_call_alternative_set P q d p" "y |\<in>| finite_call_alternative_set P q d p"
    and "finite_alternative_key x = finite_alternative_key y"
  shows "x = y"
proof -
  obtain i c S u where x: "x = (i,c,S,u)" by (rule prod_cases4)
  obtain i' c' S' u' where y: "y = (i',c',S',u')" by (rule prod_cases4)
  show ?thesis using assms unfolding x y by (auto simp: finite_call_alternative_member finite_alternative_key_def)
qed

lemma fcard_eq_by_key:
  assumes "\<And>x y. x |\<in>| A \<Longrightarrow> y |\<in>| A \<Longrightarrow> k x = k y \<Longrightarrow> x = y"
    and "\<And>x y. x |\<in>| B \<Longrightarrow> y |\<in>| B \<Longrightarrow> k x = k y \<Longrightarrow> x = y"
    and "k ` fset A = k ` fset B"
  shows "fcard A = fcard B"
proof -
  have "inj_on k (fset A)" by (rule inj_onI) (rule assms(1))
  moreover have "inj_on k (fset B)" by (rule inj_onI) (rule assms(2))
  ultimately have "card (k ` fset A) = fcard A" "card (k ` fset B) = fcard B"
    by (simp_all add: card_image fcard.rep_eq)
  then show ?thesis using assms(3) by simp
qed

lemma finite_call_alternative_region:
  assumes outside: "\<And>b. b |\<in>| finite_read_variables (finite_site_region P d) (finite_site_repeated P d) p \<Longrightarrow>
      \<sigma> b = Finite_Variable b"
    and fresh: "\<And>v. v |\<in>| finite_pattern_variables p \<Longrightarrow> fst (fst v) \<noteq> q"
    and images: "\<And>b v. b |\<in>| finite_pattern_variables p \<Longrightarrow> v |\<in>| finite_pattern_variables (\<sigma> b) \<Longrightarrow>
      fst (fst v) \<noteq> q"
  shows "(\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d (finite_pattern_substitute \<sigma> p)) \<longleftrightarrow>
    (\<exists>u. (i,c,S,u) |\<in>| finite_call_alternative_set P q d p)"
proof (cases "(d,i) |\<in>| finite_system_interfaces P \<and> ((d,c),S) |\<in>| finite_system_clauses P")
  case True
  let ?i = "finite_rename_apart (q,False) i" and ?h = "finite_rename_apart (q,True) (finite_schema_conclusion S)"
  have "finite_unify_pairs [(?i,p),(?h,p)] = None \<longleftrightarrow>
      finite_unify_pairs [(?i, finite_pattern_substitute \<sigma> p),(?h, finite_pattern_substitute \<sigma> p)] = None"
  proof (rule finite_unify_pairs_region)
    show "fset (finite_pattern_variables ?i) \<inter> fset (finite_pattern_variables ?h) = {}"
      by (rule finite_rename_apart_disjoint) simp
    show "fset (finite_pattern_variables ?i) \<inter> fset (finite_pattern_variables p) = {}"
      by (auto simp: finite_rename_apart_variables fimage.rep_eq dest: fresh)
    show "fset (finite_pattern_variables ?h) \<inter> fset (finite_pattern_variables p) = {}"
      by (auto simp: finite_rename_apart_variables fimage.rep_eq dest: fresh)
  next
    fix b assume "b |\<in>| finite_pattern_variables p"
    then show "fset (finite_pattern_variables (\<sigma> b)) \<inter>
        (fset (finite_pattern_variables ?i) \<union> fset (finite_pattern_variables ?h)) = {}"
      using \<open>b |\<in>| finite_pattern_variables p\<close>
      by (auto simp: finite_rename_apart_variables fimage.rep_eq dest: images)
  next
    fix b assume b: "b |\<in>| finite_read_variables (finite_pattern_region ?i |\<union>| finite_pattern_region ?h)
        (finite_pattern_repeated ?i |\<union>| finite_pattern_repeated ?h) p"
    show "\<sigma> b = Finite_Variable b"
    proof (rule outside, rule finite_read_variables_mono[OF b])
      show "fset (finite_pattern_region ?i |\<union>| finite_pattern_region ?h) \<subseteq> fset (finite_site_region P d)"
        using True by (auto intro: finite_site_region_member)
      show "fset (finite_pattern_repeated ?i |\<union>| finite_pattern_repeated ?h) \<subseteq> fset (finite_site_repeated P d)"
        using True by (auto intro: finite_site_repeated_member)
    qed
  qed
  then show ?thesis unfolding finite_call_alternative_exists using True by simp
next
  case False
  then show ?thesis unfolding finite_call_alternative_exists by blast
qed

theorem finite_goal_alternatives_region:
  assumes outside: "\<And>b. b |\<in>| finite_read_variables (finite_site_region P d) (finite_site_repeated P d) p \<Longrightarrow>
      \<sigma> b = Finite_Variable b"
    and fresh: "\<And>v. v |\<in>| finite_pattern_variables p \<Longrightarrow> fst (fst v) \<noteq> q"
    and images: "\<And>b v. b |\<in>| finite_pattern_variables p \<Longrightarrow> v |\<in>| finite_pattern_variables (\<sigma> b) \<Longrightarrow>
      fst (fst v) \<noteq> q"
  shows "finite_goal_alternatives P (Resolution_Call_Goal q r d (finite_pattern_substitute \<sigma> p)) =
    finite_goal_alternatives P (Resolution_Call_Goal q r d p)"
proof -
  have keys: "finite_alternative_key ` fset (finite_call_alternative_set P q d (finite_pattern_substitute \<sigma> p)) =
      finite_alternative_key ` fset (finite_call_alternative_set P q d p)"
  proof (rule set_eqI)
    fix y
    show "y \<in> finite_alternative_key ` fset (finite_call_alternative_set P q d (finite_pattern_substitute \<sigma> p)) \<longleftrightarrow>
        y \<in> finite_alternative_key ` fset (finite_call_alternative_set P q d p)"
    proof -
      obtain i c S where y: "y = (i,c,S)" by (rule prod_cases3)
      show ?thesis
        by (simp only: y finite_call_alternative_keys finite_call_alternative_region[OF outside fresh images])
    qed
  qed
  show ?thesis unfolding finite_goal_alternatives.simps
    by (rule fcard_eq_by_key[OF finite_call_alternative_key_inj finite_call_alternative_key_inj keys])
qed

corollary finite_goal_alternatives_linear_region:
  assumes linear: "finite_site_linear P d"
    and outside: "\<And>b. b |\<in>| finite_pattern_variables_at p (finite_site_region P d) \<Longrightarrow> \<sigma> b = Finite_Variable b"
    and fresh: "\<And>v. v |\<in>| finite_pattern_variables p \<Longrightarrow> fst (fst v) \<noteq> q"
    and images: "\<And>b v. b |\<in>| finite_pattern_variables p \<Longrightarrow> v |\<in>| finite_pattern_variables (\<sigma> b) \<Longrightarrow>
      fst (fst v) \<noteq> q"
  shows "finite_goal_alternatives P (Resolution_Call_Goal q r d (finite_pattern_substitute \<sigma> p)) =
    finite_goal_alternatives P (Resolution_Call_Goal q r d p)"
proof (rule finite_goal_alternatives_region)
  fix b assume "b |\<in>| finite_read_variables (finite_site_region P d) (finite_site_repeated P d) p"
  then show "\<sigma> b = Finite_Variable b"
    using outside by (simp add: finite_site_repeated_linear[OF linear] finite_read_variables_linear)
next
  fix v assume "v |\<in>| finite_pattern_variables p" then show "fst (fst v) \<noteq> q" by (rule fresh)
next
  fix b v assume "b |\<in>| finite_pattern_variables p" "v |\<in>| finite_pattern_variables (\<sigma> b)"
  then show "fst (fst v) \<noteq> q" by (rule images)
qed

section \<open>The shared read along a region\<close>

text \<open>
  A shared pattern is walked along a position as its projection is, and the walk stops at a reference, which
  holds no variable: at every formed shared pattern, the variables it holds at a set of positions and under a
  set of positions are its projection's, read through the caches of its nodes.
\<close>

fun shared_pattern_at :: "'a shared_pattern \<Rightarrow> bool list \<Rightarrow> 'a shared_pattern option" where
  "shared_pattern_at s [] = Some s"
| "shared_pattern_at (Shared_Node A p q) (d # w) = shared_pattern_at (if d then q else p) w"
| "shared_pattern_at s (d # w) = None"

lemma shared_pattern_at_leaves [simp]:
  "shared_pattern_at (Shared_Variable a) w = (if w = [] then Some (Shared_Variable a) else None)"
  "shared_pattern_at (Shared_Ground i) w = (if w = [] then Some (Shared_Ground i) else None)"
  by (cases w; simp)+

definition shared_pattern_variables_at :: "'a shared_pattern \<Rightarrow> bool list fset \<Rightarrow> 'a fset" where
  "shared_pattern_variables_at s W = ffilter (\<lambda>b. \<exists>w. w |\<in>| W \<and>
    shared_pattern_at s w = Some (Shared_Variable b)) (shared_pattern_variables s)"

definition shared_pattern_variables_under :: "'a shared_pattern \<Rightarrow> bool list fset \<Rightarrow> 'a fset" where
  "shared_pattern_variables_under s W = ffilter (\<lambda>b. \<exists>w. w |\<in>| W \<and>
    (\<exists>s'. shared_pattern_at s w = Some s' \<and> b |\<in>| shared_pattern_variables s')) (shared_pattern_variables s)"

definition shared_read_variables :: "bool list fset \<Rightarrow> bool list fset \<Rightarrow> 'a shared_pattern \<Rightarrow> 'a fset" where
  "shared_read_variables R D s = shared_pattern_variables_at s R |\<union>| shared_pattern_variables_under s D"

lemma shared_ground_project_variables:
  "finite_pattern_variables (shared_pattern_project T (Shared_Ground i)) = {||}"
  by (simp split: option.split)

lemma shared_pattern_at_variables_subset:
  assumes "shared_pattern_formed T s" "shared_pattern_at s w = Some s'"
  shows "fset (shared_pattern_variables s') \<subseteq> fset (shared_pattern_variables s)"
  using assms
proof (induction s arbitrary: w)
  case (Shared_Node A p q)
  show ?case
  proof (cases w)
    case Nil then show ?thesis using Shared_Node.prems by simp
  next
    case (Cons d w')
    then show ?thesis using Shared_Node by (cases d) auto
  qed
qed (auto split: if_splits)

lemma shared_pattern_at_variable:
  assumes "shared_pattern_formed T s"
  shows "shared_pattern_at s w = Some (Shared_Variable a) \<longleftrightarrow>
    finite_pattern_at (shared_pattern_project T s) w = Some (Finite_Variable a)"
  using assms
proof (induction s arbitrary: w)
  case (Shared_Variable x) then show ?case by auto
next
  case (Shared_Ground i)
  have "finite_pattern_at (shared_pattern_project T (Shared_Ground i)) w \<noteq> Some (Finite_Variable a)"
    using finite_pattern_at_variable_member shared_ground_project_variables by fastforce
  then show ?case by auto
next
  case (Shared_Node A p q)
  show ?case
  proof (cases w)
    case Nil then show ?thesis by simp
  next
    case (Cons d w') then show ?thesis using Shared_Node by (cases d) simp_all
  qed
qed

lemma shared_pattern_at_variables:
  assumes "shared_pattern_formed T s"
  shows "(\<exists>s'. shared_pattern_at s w = Some s' \<and> b |\<in>| shared_pattern_variables s') \<longleftrightarrow>
    (\<exists>g. finite_pattern_at (shared_pattern_project T s) w = Some g \<and> b |\<in>| finite_pattern_variables g)"
  using assms
proof (induction s arbitrary: w)
  case (Shared_Variable x) then show ?case by auto
next
  case (Shared_Ground i)
  have "b |\<notin>| finite_pattern_variables g" if "finite_pattern_at (shared_pattern_project T (Shared_Ground i)) w = Some g" for g
    using finite_pattern_at_variables[OF that] shared_ground_project_variables[of T i] by auto
  then show ?case by auto
next
  case (Shared_Node A p q)
  show ?case
  proof (cases w)
    case Nil
    have "b |\<in>| shared_pattern_variables p \<longleftrightarrow> b |\<in>| finite_pattern_variables (shared_pattern_project T p)"
      using Shared_Node.IH(1)[of "[]"] Shared_Node.prems by simp
    moreover have "b |\<in>| shared_pattern_variables q \<longleftrightarrow> b |\<in>| finite_pattern_variables (shared_pattern_project T q)"
      using Shared_Node.IH(2)[of "[]"] Shared_Node.prems by simp
    ultimately show ?thesis using Nil Shared_Node.prems by auto
  next
    case (Cons d w') then show ?thesis using Shared_Node by (cases d) simp_all
  qed
qed

theorem shared_pattern_variables_at_project:
  assumes "shared_pattern_formed T s"
  shows "shared_pattern_variables_at s W = finite_pattern_variables_at (shared_pattern_project T s) W"
proof (rule fset_eqI)
  fix b
  have "b |\<in>| shared_pattern_variables s" if "shared_pattern_at s w = Some (Shared_Variable b)" for w
    using shared_pattern_at_variables_subset[OF assms that] by auto
  then show "b |\<in>| shared_pattern_variables_at s W \<longleftrightarrow>
      b |\<in>| finite_pattern_variables_at (shared_pattern_project T s) W"
    unfolding finite_pattern_variables_at_member shared_pattern_variables_at_def ffmember_filter
    using shared_pattern_at_variable[OF assms] by blast
qed

theorem shared_pattern_variables_under_project:
  assumes "shared_pattern_formed T s"
  shows "shared_pattern_variables_under s W = finite_pattern_variables_under (shared_pattern_project T s) W"
proof (rule fset_eqI)
  fix b
  have "b |\<in>| shared_pattern_variables s"
    if "shared_pattern_at s w = Some s'" "b |\<in>| shared_pattern_variables s'" for w s'
    using shared_pattern_at_variables_subset[OF assms that(1)] that(2) by auto
  then show "b |\<in>| shared_pattern_variables_under s W \<longleftrightarrow>
      b |\<in>| finite_pattern_variables_under (shared_pattern_project T s) W"
    unfolding finite_pattern_variables_under_member shared_pattern_variables_under_def ffmember_filter
    using shared_pattern_at_variables[OF assms] by blast
qed

theorem shared_read_variables_project:
  assumes "shared_pattern_formed T s"
  shows "shared_read_variables R D s = finite_read_variables R D (shared_pattern_project T s)"
  by (simp add: shared_read_variables_def finite_read_variables_def
    shared_pattern_variables_at_project[OF assms] shared_pattern_variables_under_project[OF assms])

end
