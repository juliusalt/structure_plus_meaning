theory Factor_Finite_Schema_Matching
  imports Factor_Pattern_Unification Factor_Alpha_Semantics Finite_Functional_Enumeration
begin

section \<open>A clause matched against its alpha variant\<close>

text \<open>
  Two finite clauses are alpha variants when one is the other renamed by binder and socket maps injective on its
  scope, callees kept (@{const schema_alpha_variant}). The match below finds such maps, or finds that none exist:
  it matches the conclusions first, then pairs every premise of the first clause with a premise of the second —
  call premises by callee, material premises field by field — extending the binder map injectively at each
  pairing and backtracking where a pairing fails later. It reads constructors, callee sites and the identity of
  coordinates, as matching does, and nothing else; it changes no clause.
\<close>

subsection \<open>An injective binder graph extended by pattern matching\<close>

definition finite_injective_graph :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "finite_injective_graph F \<longleftrightarrow> distinct (map fst F) \<and> distinct (map snd F)"

lemma finite_injective_graph_empty [simp]: "finite_injective_graph []"
  by (simp add: finite_injective_graph_def)

lemma finite_injective_graph_value:
  assumes "(a,b) \<in> set G" "distinct (map fst G)"
  shows "the (map_of G a) = b"
  using assms by (simp add: map_of_is_SomeI)

lemma finite_injective_graph_inj:
  assumes graph: "finite_injective_graph G"
  shows "inj_on (\<lambda>a. the (map_of G a)) (fst ` set G)"
proof (rule inj_onI)
  fix a a' assume here: "a \<in> fst ` set G" and there: "a' \<in> fst ` set G"
    and same: "the (map_of G a) = the (map_of G a')"
  have keys: "distinct (map fst G)" and field_values: "inj_on snd (set G)"
    using graph by (simp_all add: finite_injective_graph_def distinct_map)
  obtain b where b: "(a,b) \<in> set G" using here by force
  obtain b' where b': "(a',b') \<in> set G" using there by force
  have "b = b'" using same finite_injective_graph_value[OF b keys] finite_injective_graph_value[OF b' keys] by simp
  then have "(a,b) = (a',b')" using inj_onD[OF field_values _ b b'] by simp
  then show "a = a'" by simp
qed

fun finite_rename_match ::
  "('a \<times> 'b) list \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'b finite_term_pattern \<Rightarrow> ('a \<times> 'b) list option" where
  "finite_rename_match F (Finite_Variable a) (Finite_Variable b) =
    (case map_of F a of Some c \<Rightarrow> if c = b then Some F else None
     | None \<Rightarrow> if b \<in> set (map snd F) then None else Some ((a,b)#F))"
| "finite_rename_match F (Finite_Pattern_Target x) (Finite_Pattern_Target y) = (if x = y then Some F else None)"
| "finite_rename_match F (Finite_Pattern_Payload v) (Finite_Pattern_Payload w) = (if v = w then Some F else None)"
| "finite_rename_match F (Finite_Pattern_Pair p q) (Finite_Pattern_Pair p' q') =
    (case finite_rename_match F p p' of None \<Rightarrow> None | Some G \<Rightarrow> finite_rename_match G q q')"
| "finite_rename_match F _ _ = None"

lemma finite_rename_match_sound:
  assumes "finite_rename_match F p q = Some G" "finite_injective_graph F"
  shows "finite_injective_graph G \<and> set F \<subseteq> set G \<and> fset (finite_pattern_variables p) \<subseteq> fst ` set G \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      map_finite_term_pattern (\<lambda>a. the (map_of K a)) p = q)"
  using assms
proof (induction F p q arbitrary: G rule: finite_rename_match.induct)
  case (1 F a b)
  show ?case
  proof (cases "map_of F a")
    case None
    have fresh: "b \<notin> set (map snd F)" and result: "G = (a,b)#F"
      using "1.prems"(1) None by (auto split: if_splits)
    have absent: "a \<notin> set (map fst F)" using None by (auto simp: map_of_eq_None_iff)
    have graph: "finite_injective_graph G"
      using "1.prems"(2) fresh absent by (simp add: result finite_injective_graph_def)
    have valued: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> the (map_of K a) = b"
      by (auto simp: result map_of_is_SomeI)
    show ?thesis using graph valued by (auto simp: result)
  next
    case (Some c)
    have result: "c = b" "G = F" using "1.prems"(1) Some by (auto split: if_splits)
    have member: "(a,b) \<in> set F" using Some result(1) by (auto dest: map_of_SomeD)
    have valued: "\<forall>K. set F \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> the (map_of K a) = b"
      using member by (auto simp: map_of_is_SomeI)
    show ?thesis using "1.prems"(2) member valued by (force simp: result)
  qed
next
  case (4 F p q p' q')
  obtain G1 where first: "finite_rename_match F p p' = Some G1"
    and second: "finite_rename_match G1 q q' = Some G"
    using "4.prems"(1) by (auto split: option.splits)
  have L: "finite_injective_graph G1 \<and> set F \<subseteq> set G1 \<and> fset (finite_pattern_variables p) \<subseteq> fst ` set G1 \<and>
    (\<forall>K. set G1 \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> map_finite_term_pattern (\<lambda>a. the (map_of K a)) p = p')"
    by (rule "4.IH"(1)[OF first "4.prems"(2)])
  have R: "finite_injective_graph G \<and> set G1 \<subseteq> set G \<and> fset (finite_pattern_variables q) \<subseteq> fst ` set G \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> map_finite_term_pattern (\<lambda>a. the (map_of K a)) q = q')"
    using "4.IH"(2)[OF first second] L by blast
  have within: "fst ` set G1 \<subseteq> fst ` set G" using R by (simp add: image_mono)
  have maps: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      map_finite_term_pattern (\<lambda>a. the (map_of K a)) (Finite_Pattern_Pair p q) = Finite_Pattern_Pair p' q'"
  proof (intro allI impI)
    fix K :: "('a \<times> 'b) list" assume K: "set G \<subseteq> set K" "distinct (map fst K)"
    have inner: "set G1 \<subseteq> set K" using R K(1) by blast
    have left: "map_finite_term_pattern (\<lambda>a. the (map_of K a)) p = p'" using L inner K(2) by blast
    have right: "map_finite_term_pattern (\<lambda>a. the (map_of K a)) q = q'" using R K by blast
    show "map_finite_term_pattern (\<lambda>a. the (map_of K a)) (Finite_Pattern_Pair p q) = Finite_Pattern_Pair p' q'"
      by (simp add: left right)
  qed
  show ?case using L R within maps by (auto simp: sup_fset.rep_eq)
qed (auto split: if_splits)

lemma finite_rename_match_complete:
  assumes "inj_on g (fst ` set F \<union> fset (finite_pattern_variables p))"
    and "\<forall>z\<in>set F. g (fst z) = snd z" and "finite_injective_graph F"
  shows "\<exists>G. finite_rename_match F p (map_finite_term_pattern g p) = Some G \<and>
    (\<forall>z\<in>set G. g (fst z) = snd z) \<and> fst ` set G = fst ` set F \<union> fset (finite_pattern_variables p)"
  using assms
proof (induction p arbitrary: F)
  case (Finite_Variable a)
  show ?case
  proof (cases "map_of F a")
    case None
    have absent: "a \<notin> fst ` set F" using None by (simp add: map_of_eq_None_iff)
    have fresh: "g a \<notin> set (map snd F)"
    proof
      assume "g a \<in> set (map snd F)"
      then obtain z where z: "z \<in> set F" "snd z = g a" by auto
      have image: "g (fst z) = g a" using Finite_Variable.prems(2) z by auto
      have "fst z = a"
        by (rule inj_onD[OF Finite_Variable.prems(1) image]) (use z(1) in auto)
      then show False using absent z(1) by auto
    qed
    show ?thesis using None fresh Finite_Variable.prems(2)
      by (intro exI[of _ "(a,g a)#F"]) auto
  next
    case (Some c)
    have member: "(a,c) \<in> set F" using Some by (rule map_of_SomeD)
    have valued: "g a = c" using Finite_Variable.prems(2) member by auto
    show ?thesis using Some valued Finite_Variable.prems(2) member
      by (intro exI[of _ F]) force
  qed
next
  case (Finite_Pattern_Target x)
  then show ?case by simp
next
  case (Finite_Pattern_Payload v)
  then show ?case by simp
next
  case (Finite_Pattern_Pair p q)
  have first_scope: "inj_on g (fst ` set F \<union> fset (finite_pattern_variables p))"
    by (rule inj_on_subset[OF Finite_Pattern_Pair.prems(1)]) (auto simp: sup_fset.rep_eq)
  obtain G1 where first: "finite_rename_match F p (map_finite_term_pattern g p) = Some G1"
    and agree1: "\<forall>z\<in>set G1. g (fst z) = snd z"
    and domain1: "fst ` set G1 = fst ` set F \<union> fset (finite_pattern_variables p)"
    using Finite_Pattern_Pair.IH(1)[OF first_scope Finite_Pattern_Pair.prems(2,3)] by blast
  have graph1: "finite_injective_graph G1"
    using finite_rename_match_sound[OF first Finite_Pattern_Pair.prems(3)] by blast
  have second_scope: "inj_on g (fst ` set G1 \<union> fset (finite_pattern_variables q))"
    by (rule inj_on_subset[OF Finite_Pattern_Pair.prems(1)]) (auto simp: domain1 sup_fset.rep_eq)
  obtain G where second: "finite_rename_match G1 q (map_finite_term_pattern g q) = Some G"
    and agree: "\<forall>z\<in>set G. g (fst z) = snd z"
    and domain: "fst ` set G = fst ` set G1 \<union> fset (finite_pattern_variables q)"
    using Finite_Pattern_Pair.IH(2)[OF second_scope agree1 graph1] by blast
  show ?case using first second agree domain domain1
    by (intro exI[of _ G]) (auto simp: sup_fset.rep_eq)
qed

subsection \<open>Lists of patterns: the five fields of a material premise\<close>

fun finite_rename_match_list ::
  "('a \<times> 'b) list \<Rightarrow> 'a finite_term_pattern list \<Rightarrow> 'b finite_term_pattern list \<Rightarrow> ('a \<times> 'b) list option" where
  "finite_rename_match_list F [] [] = Some F"
| "finite_rename_match_list F (p#ps) (q#qs) =
    (case finite_rename_match F p q of None \<Rightarrow> None | Some G \<Rightarrow> finite_rename_match_list G ps qs)"
| "finite_rename_match_list F _ _ = None"

lemma finite_rename_match_list_sound:
  assumes "finite_rename_match_list F ps qs = Some G" "finite_injective_graph F"
  shows "finite_injective_graph G \<and> set F \<subseteq> set G \<and>
    (\<Union>p\<in>set ps. fset (finite_pattern_variables p)) \<subseteq> fst ` set G \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) ps = qs)"
  using assms
proof (induction ps arbitrary: F qs)
  case Nil
  then show ?case by (cases qs) auto
next
  case (Cons p ps)
  obtain q qs' where qs: "qs = q#qs'" using Cons.prems(1) by (cases qs) auto
  obtain G1 where first: "finite_rename_match F p q = Some G1"
    and rest: "finite_rename_match_list G1 ps qs' = Some G"
    using Cons.prems(1) qs by (auto split: option.splits)
  note P = finite_rename_match_sound[OF first Cons.prems(2)]
  have R: "finite_injective_graph G \<and> set G1 \<subseteq> set G \<and>
    (\<Union>p\<in>set ps. fset (finite_pattern_variables p)) \<subseteq> fst ` set G \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) ps = qs')"
    using Cons.IH[OF rest] P by blast
  have within: "fst ` set G1 \<subseteq> fst ` set G" using R by (simp add: image_mono)
  have maps: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) (p#ps) = qs"
  proof (intro allI impI)
    fix K :: "('a \<times> 'b) list" assume K: "set G \<subseteq> set K" "distinct (map fst K)"
    have inner: "set G1 \<subseteq> set K" using R K(1) by blast
    have here: "map_finite_term_pattern (\<lambda>a. the (map_of K a)) p = q" using P inner K(2) by blast
    have there: "map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) ps = qs'" using R K by blast
    show "map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) (p#ps) = qs" by (simp add: qs here there)
  qed
  show ?case using P R within maps by auto
qed

lemma finite_rename_match_list_complete:
  assumes "inj_on g (fst ` set F \<union> (\<Union>p\<in>set ps. fset (finite_pattern_variables p)))"
    and "\<forall>z\<in>set F. g (fst z) = snd z" and "finite_injective_graph F"
  shows "\<exists>G. finite_rename_match_list F ps (map (map_finite_term_pattern g) ps) = Some G \<and>
    (\<forall>z\<in>set G. g (fst z) = snd z) \<and>
    fst ` set G = fst ` set F \<union> (\<Union>p\<in>set ps. fset (finite_pattern_variables p))"
  using assms
proof (induction ps arbitrary: F)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  have first_scope: "inj_on g (fst ` set F \<union> fset (finite_pattern_variables p))"
    by (rule inj_on_subset[OF Cons.prems(1)]) auto
  obtain G1 where first: "finite_rename_match F p (map_finite_term_pattern g p) = Some G1"
    and agree1: "\<forall>z\<in>set G1. g (fst z) = snd z"
    and domain1: "fst ` set G1 = fst ` set F \<union> fset (finite_pattern_variables p)"
    using finite_rename_match_complete[OF first_scope Cons.prems(2,3)] by blast
  have graph1: "finite_injective_graph G1" using finite_rename_match_sound[OF first Cons.prems(3)] by blast
  have rest_scope: "inj_on g (fst ` set G1 \<union> (\<Union>p\<in>set ps. fset (finite_pattern_variables p)))"
    by (rule inj_on_subset[OF Cons.prems(1)]) (auto simp: domain1)
  obtain G where rest: "finite_rename_match_list G1 ps (map (map_finite_term_pattern g) ps) = Some G"
    and agree: "\<forall>z\<in>set G. g (fst z) = snd z"
    and domain: "fst ` set G = fst ` set G1 \<union> (\<Union>p\<in>set ps. fset (finite_pattern_variables p))"
    using Cons.IH[OF rest_scope agree1 graph1] by blast
  show ?case using first rest agree domain domain1 by (intro exI[of _ G]) auto
qed

definition finite_material_field_list :: "'a finite_material_pattern \<Rightarrow> 'a finite_term_pattern list" where
  "finite_material_field_list M = [finite_material_source M, finite_material_atoms M,
    finite_material_edges M, finite_material_counts M, finite_material_functions M]"

lemma finite_material_field_list_rename:
  "finite_material_field_list (finite_rename_material f M) =
    map (map_finite_term_pattern f) (finite_material_field_list M)"
  by (simp add: finite_material_field_list_def finite_rename_material_def)

lemma finite_material_field_list_inject:
  "finite_material_field_list M = finite_material_field_list N \<longleftrightarrow> M = N"
  by (cases M; cases N) (simp add: finite_material_field_list_def)

lemma finite_material_field_list_variables:
  "fset (finite_material_variables M) = (\<Union>p\<in>set (finite_material_field_list M). fset (finite_pattern_variables p))"
  by (auto simp: finite_material_variables_def finite_material_field_list_def sup_fset.rep_eq)

subsection \<open>Premises: a call by its callee, a material premise by its five fields\<close>

type_synonym ('a,'d) finite_premise_form = "('d \<times> 'a finite_term_pattern) + 'a finite_material_pattern"

fun finite_premise_form_variables :: "('a,'d) finite_premise_form \<Rightarrow> 'a fset" where
  "finite_premise_form_variables (Inl c) = finite_pattern_variables (snd c)"
| "finite_premise_form_variables (Inr M) = finite_material_variables M"

fun finite_rename_premise :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'d) finite_premise_form \<Rightarrow> ('b,'d) finite_premise_form" where
  "finite_rename_premise f (Inl c) = Inl (fst c,map_finite_term_pattern f (snd c))"
| "finite_rename_premise f (Inr M) = Inr (finite_rename_material f M)"

fun finite_rename_match_premise ::
  "('a \<times> 'b) list \<Rightarrow> ('a,'d) finite_premise_form \<Rightarrow> ('b,'d) finite_premise_form \<Rightarrow> ('a \<times> 'b) list option" where
  "finite_rename_match_premise F (Inl c) (Inl c') =
    (if fst c = fst c' then finite_rename_match F (snd c) (snd c') else None)"
| "finite_rename_match_premise F (Inr M) (Inr N) =
    finite_rename_match_list F (finite_material_field_list M) (finite_material_field_list N)"
| "finite_rename_match_premise F _ _ = None"

lemma finite_rename_match_premise_sound:
  assumes match: "finite_rename_match_premise F x y = Some G" and graph: "finite_injective_graph F"
  shows "finite_injective_graph G \<and> set F \<subseteq> set G \<and> fset (finite_premise_form_variables x) \<subseteq> fst ` set G \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> finite_rename_premise (\<lambda>a. the (map_of K a)) x = y)"
proof (cases x)
  case (Inl c)
  obtain c' where y: "y = Inl c'" and callee: "fst c = fst c'"
    and pattern: "finite_rename_match F (snd c) (snd c') = Some G"
    using match Inl by (cases y) (auto split: if_splits)
  note P = finite_rename_match_sound[OF pattern graph]
  have maps: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> finite_rename_premise (\<lambda>a. the (map_of K a)) x = y"
  proof (intro allI impI)
    fix K :: "('a \<times> 'b) list" assume K: "set G \<subseteq> set K" "distinct (map fst K)"
    have "map_finite_term_pattern (\<lambda>a. the (map_of K a)) (snd c) = snd c'" using P K by blast
    then show "finite_rename_premise (\<lambda>a. the (map_of K a)) x = y" using Inl y callee by (cases c') simp
  qed
  show ?thesis using P maps Inl by simp
next
  case (Inr M)
  obtain N where y: "y = Inr N"
    and fields: "finite_rename_match_list F (finite_material_field_list M) (finite_material_field_list N) = Some G"
    using match Inr by (cases y) auto
  note P = finite_rename_match_list_sound[OF fields graph]
  have maps: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow> finite_rename_premise (\<lambda>a. the (map_of K a)) x = y"
  proof (intro allI impI)
    fix K :: "('a \<times> 'b) list" assume K: "set G \<subseteq> set K" "distinct (map fst K)"
    have "map (map_finite_term_pattern (\<lambda>a. the (map_of K a))) (finite_material_field_list M) =
        finite_material_field_list N" using P K by blast
    then have "finite_rename_material (\<lambda>a. the (map_of K a)) M = N"
      by (simp flip: finite_material_field_list_inject add: finite_material_field_list_rename)
    then show "finite_rename_premise (\<lambda>a. the (map_of K a)) x = y" by (simp add: Inr y)
  qed
  show ?thesis using P maps Inr by (simp add: finite_material_field_list_variables)
qed

lemma finite_rename_match_premise_complete:
  assumes scope: "inj_on g (fst ` set F \<union> fset (finite_premise_form_variables x))"
    and agree: "\<forall>z\<in>set F. g (fst z) = snd z" and graph: "finite_injective_graph F"
  shows "\<exists>G. finite_rename_match_premise F x (finite_rename_premise g x) = Some G \<and>
    (\<forall>z\<in>set G. g (fst z) = snd z) \<and> fst ` set G = fst ` set F \<union> fset (finite_premise_form_variables x)"
proof (cases x)
  case (Inl c)
  have "inj_on g (fst ` set F \<union> fset (finite_pattern_variables (snd c)))" using scope Inl by simp
  from finite_rename_match_complete[OF this agree graph] show ?thesis using Inl by simp
next
  case (Inr M)
  have "inj_on g (fst ` set F \<union> (\<Union>p\<in>set (finite_material_field_list M). fset (finite_pattern_variables p)))"
    using scope Inr by (simp add: finite_material_field_list_variables)
  from finite_rename_match_list_complete[OF this agree graph] show ?thesis
    using Inr by (simp add: finite_material_field_list_rename finite_material_field_list_variables)
qed

subsection \<open>Every premise paired, backtracking over the candidates\<close>

primrec finite_first_some :: "('c \<Rightarrow> 'r option) \<Rightarrow> 'c list \<Rightarrow> 'r option" where
  "finite_first_some g [] = None"
| "finite_first_some g (y#ys) = (case g y of None \<Rightarrow> finite_first_some g ys | Some r \<Rightarrow> Some r)"

lemma finite_first_some_cong [fundef_cong]:
  assumes "xs = ys" "\<And>y. y \<in> set ys \<Longrightarrow> g y = g' y"
  shows "finite_first_some g xs = finite_first_some g' ys"
proof -
  have "finite_first_some g ys = finite_first_some g' ys" using assms(2)
  proof (induction ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a ys)
    have head: "g a = g' a" using Cons.prems by simp
    have tail: "finite_first_some g ys = finite_first_some g' ys" by (rule Cons.IH) (simp add: Cons.prems)
    show ?case by (simp only: finite_first_some.simps head tail)
  qed
  then show ?thesis using assms(1) by simp
qed

lemma finite_first_some_Some: "finite_first_some g ys = Some r \<Longrightarrow> \<exists>y\<in>set ys. g y = Some r"
  by (induction ys) (auto split: option.splits)

lemma finite_first_some_member: "y \<in> set ys \<Longrightarrow> g y \<noteq> None \<Longrightarrow> finite_first_some g ys \<noteq> None"
  by (induction ys) (auto split: option.splits)

fun finite_rename_match_rows ::
  "('a \<times> 'b) list \<Rightarrow> ('s \<times> ('a,'d) finite_premise_form) list \<Rightarrow> ('t \<times> ('b,'d) finite_premise_form) list \<Rightarrow>
    (('a \<times> 'b) list \<times> 't list) option" where
  "finite_rename_match_rows F [] ys = (if ys = [] then Some (F,[]) else None)"
| "finite_rename_match_rows F ((s,x)#xs) ys = finite_first_some (\<lambda>(t,y).
    case finite_rename_match_premise F x y of None \<Rightarrow> None
    | Some G \<Rightarrow> map_option (\<lambda>(K,ts). (K,t#ts)) (finite_rename_match_rows G xs (remove1 (t,y) ys))) ys"

lemma finite_rename_match_rows_sound:
  assumes "finite_rename_match_rows F xs ys = Some (G,ts)" "finite_injective_graph F"
  shows "finite_injective_graph G \<and> set F \<subseteq> set G \<and> length ts = length xs \<and>
    (\<forall>z\<in>set xs. fset (finite_premise_form_variables (snd z)) \<subseteq> fst ` set G) \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      mset ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise (\<lambda>a. the (map_of K a)) (snd z))) xs ts))"
  using assms
proof (induction xs arbitrary: F ys G ts)
  case Nil
  then show ?case by (auto split: if_splits)
next
  case (Cons z xs)
  obtain s x where z: "z = (s,x)" by (cases z)
  from Cons.prems(1) obtain t y where member: "(t,y) \<in> set ys"
    and step: "(case finite_rename_match_premise F x y of None \<Rightarrow> None
      | Some G' \<Rightarrow> map_option (\<lambda>(K,ts). (K,t#ts)) (finite_rename_match_rows G' xs (remove1 (t,y) ys))) = Some (G,ts)"
    by (auto simp: z dest!: finite_first_some_Some)
  obtain G1 where premise: "finite_rename_match_premise F x y = Some G1"
    and rest: "map_option (\<lambda>(K,ts). (K,t#ts)) (finite_rename_match_rows G1 xs (remove1 (t,y) ys)) = Some (G,ts)"
    using step by (auto split: option.splits)
  obtain ts' where tail: "finite_rename_match_rows G1 xs (remove1 (t,y) ys) = Some (G,ts')" and ts: "ts = t#ts'"
    using rest by auto
  note P = finite_rename_match_premise_sound[OF premise Cons.prems(2)]
  have R: "finite_injective_graph G \<and> set G1 \<subseteq> set G \<and> length ts' = length xs \<and>
    (\<forall>z\<in>set xs. fset (finite_premise_form_variables (snd z)) \<subseteq> fst ` set G) \<and>
    (\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      mset (remove1 (t,y) ys) = mset (map2 (\<lambda>z t. (t,finite_rename_premise (\<lambda>a. the (map_of K a)) (snd z))) xs ts'))"
    using Cons.IH[OF tail] P by blast
  have within: "fst ` set G1 \<subseteq> fst ` set G" using R by (simp add: image_mono)
  have maps: "\<forall>K. set G \<subseteq> set K \<longrightarrow> distinct (map fst K) \<longrightarrow>
      mset ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise (\<lambda>a. the (map_of K a)) (snd z))) (z#xs) ts)"
  proof (intro allI impI)
    fix K :: "('a \<times> 'b) list" assume K: "set G \<subseteq> set K" "distinct (map fst K)"
    have inner: "set G1 \<subseteq> set K" using R K(1) by blast
    have here: "finite_rename_premise (\<lambda>a. the (map_of K a)) x = y" using P inner K(2) by blast
    have there: "mset (remove1 (t,y) ys) =
        mset (map2 (\<lambda>z t. (t,finite_rename_premise (\<lambda>a. the (map_of K a)) (snd z))) xs ts')" using R K by blast
    have whole: "mset ys = add_mset (t,y) (mset (remove1 (t,y) ys))" using member by (simp add: insert_DiffM)
    show "mset ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise (\<lambda>a. the (map_of K a)) (snd z))) (z#xs) ts)"
      using whole here there by (simp add: z ts)
  qed
  show ?case using P R within maps by (auto simp: z ts)
qed

lemma finite_rename_match_rows_complete:
  assumes "inj_on g (fst ` set F \<union> (\<Union>z\<in>set xs. fset (finite_premise_form_variables (snd z))))"
    and "\<forall>z\<in>set F. g (fst z) = snd z" and "finite_injective_graph F"
    and "length ts = length xs"
    and "mset ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise g (snd z))) xs ts)"
  shows "finite_rename_match_rows F xs ys \<noteq> None"
  using assms
proof (induction xs arbitrary: F ys ts)
  case Nil
  then show ?case by simp
next
  case (Cons z xs)
  obtain s x where z: "z = (s,x)" by (cases z)
  obtain t ts' where ts: "ts = t#ts'" using Cons.prems(4) by (cases ts) auto
  have whole: "mset ys = add_mset (t,finite_rename_premise g x)
      (mset (map2 (\<lambda>z t. (t,finite_rename_premise g (snd z))) xs ts'))"
    using Cons.prems(5) by (simp add: z ts)
  have member: "(t,finite_rename_premise g x) \<in> set ys"
    using arg_cong[OF whole, of set_mset] by simp
  have rest_rows: "mset (remove1 (t,finite_rename_premise g x) ys) =
      mset (map2 (\<lambda>z t. (t,finite_rename_premise g (snd z))) xs ts')"
    using whole by simp
  have here_scope: "inj_on g (fst ` set F \<union> fset (finite_premise_form_variables x))"
    by (rule inj_on_subset[OF Cons.prems(1)]) (auto simp: z)
  obtain G1 where premise: "finite_rename_match_premise F x (finite_rename_premise g x) = Some G1"
    and agree1: "\<forall>z\<in>set G1. g (fst z) = snd z"
    and domain1: "fst ` set G1 = fst ` set F \<union> fset (finite_premise_form_variables x)"
    using finite_rename_match_premise_complete[OF here_scope Cons.prems(2,3)] by blast
  have graph1: "finite_injective_graph G1"
    using finite_rename_match_premise_sound[OF premise Cons.prems(3)] by blast
  have rest_scope: "inj_on g (fst ` set G1 \<union> (\<Union>z\<in>set xs. fset (finite_premise_form_variables (snd z))))"
    by (rule inj_on_subset[OF Cons.prems(1)]) (auto simp: domain1 z)
  have length: "length ts' = length xs" using Cons.prems(4) ts by simp
  have rest: "finite_rename_match_rows G1 xs (remove1 (t,finite_rename_premise g x) ys) \<noteq> None"
    by (rule Cons.IH[OF rest_scope agree1 graph1 length rest_rows])
  show ?case unfolding z finite_rename_match_rows.simps(2)
    by (rule finite_first_some_member[OF member]) (simp add: premise rest)
qed

subsection \<open>The premises of a formed clause as rows, keyed by their sockets\<close>

definition finite_schema_rows ::
  "('a,'s::linorder,'d) finite_factor_schema \<Rightarrow> ('s \<times> ('a,'d) finite_premise_form) list" where
  "finite_schema_rows S =
    map (\<lambda>z. (fst z,Inl (snd z))) (finite_functional_rows (finite_schema_premises S)) @
    map (\<lambda>z. (fst z,Inr (snd z))) (finite_functional_rows (finite_schema_materials S))"

lemma finite_schema_sockets_decoded:
  "schema_sockets (decode_finite_schema S) =
    fst ` fset (finite_schema_premises S) \<union> fst ` fset (finite_schema_materials S)"
  by (simp add: schema_sockets_def rel_dom_image)

lemma finite_schema_rows_set:
  assumes "finite_schema_formed S"
  shows "set (finite_schema_rows S) = (\<lambda>z. (fst z,Inl (snd z))) ` fset (finite_schema_premises S) \<union>
    (\<lambda>z. (fst z,Inr (snd z))) ` fset (finite_schema_materials S)"
  using assms by (simp add: finite_schema_rows_def finite_schema_formed_def finite_functional_rows_exact)

lemma finite_schema_rows_member:
  assumes "finite_schema_formed S"
  shows "(s,Inl c) \<in> set (finite_schema_rows S) \<longleftrightarrow> (s,c) |\<in>| finite_schema_premises S"
    and "(s,Inr M) \<in> set (finite_schema_rows S) \<longleftrightarrow> (s,M) |\<in>| finite_schema_materials S"
  by (force simp: finite_schema_rows_set[OF assms])+

lemma finite_schema_rows_keys:
  assumes "finite_schema_formed S"
  shows "distinct (map fst (finite_schema_rows S))"
    and "set (map fst (finite_schema_rows S)) = schema_sockets (decode_finite_schema S)"
proof -
  have calls: "finite_relation_functional (finite_schema_premises S)"
    and materials: "finite_relation_functional (finite_schema_materials S)"
    and apart: "fimage fst (finite_schema_premises S) |\<inter>| fimage fst (finite_schema_materials S) = {||}"
    using assms by (simp_all add: finite_schema_formed_def)
  have keys: "map fst (finite_schema_rows S) = sorted_list_of_fset (fimage fst (finite_schema_premises S)) @
      sorted_list_of_fset (fimage fst (finite_schema_materials S))"
    by (simp add: finite_schema_rows_def comp_def finite_functional_rows_keys[OF calls, symmetric]
      finite_functional_rows_keys[OF materials, symmetric])
  have disjoint: "fset (fimage fst (finite_schema_premises S)) \<inter> fset (fimage fst (finite_schema_materials S)) = {}"
    using apart by (metis bot_fset.rep_eq inf_fset.rep_eq)
  show "distinct (map fst (finite_schema_rows S))" using disjoint by (simp add: keys)
  show "set (map fst (finite_schema_rows S)) = schema_sockets (decode_finite_schema S)"
    by (simp add: keys finite_schema_sockets_decoded fimage.rep_eq)
qed

lemma finite_schema_rows_variables:
  assumes "finite_schema_formed S"
  shows "schema_variables (decode_finite_schema S) = fset (finite_pattern_variables (finite_schema_conclusion S)) \<union>
    (\<Union>z\<in>set (finite_schema_rows S). fset (finite_premise_form_variables (snd z)))"
  by (auto simp: finite_schema_variables_correct[symmetric] finite_schema_variables_def ffUnion.rep_eq
      fimage.rep_eq sup_fset.rep_eq finite_schema_rows_set[OF assms] split: prod.splits)

lemma finite_rows_zip_values:
  assumes "length ts = length xs" "distinct (map fst xs)"
  shows "map2 (\<lambda>z t. (t,r z)) xs ts = map (\<lambda>z. (the (map_of (zip (map fst xs) ts) (fst z)),r z)) xs"
  using assms
proof (induction xs arbitrary: ts)
  case Nil
  then show ?case by simp
next
  case (Cons z xs)
  obtain t ts' where ts: "ts = t#ts'" using Cons.prems(1) by (cases ts) auto
  have IH: "map2 (\<lambda>z t. (t,r z)) xs ts' = map (\<lambda>z. (the (map_of (zip (map fst xs) ts') (fst z)),r z)) xs"
    by (rule Cons.IH) (use Cons.prems ts in auto)
  have fresh: "fst z \<notin> fst ` set xs" using Cons.prems(2) by simp
  have rest: "map (\<lambda>w. (the (map_of (zip (map fst (z#xs)) ts) (fst w)),r w)) xs =
      map (\<lambda>w. (the (map_of (zip (map fst xs) ts') (fst w)),r w)) xs"
  proof (rule map_cong[OF refl])
    fix w assume member: "w \<in> set xs"
    have "fst w \<in> fst ` set xs" using member by (rule imageI)
    then have "fst w \<noteq> fst z" using fresh by metis
    then show "(the (map_of (zip (map fst (z#xs)) ts) (fst w)),r w) =
        (the (map_of (zip (map fst xs) ts') (fst w)),r w)" by (simp add: ts)
  qed
  show ?case using IH rest by (simp add: ts)
qed

lemma finite_rows_zip_keys:
  "length ts = length xs \<Longrightarrow> map fst (map2 (\<lambda>z t. (t,r z)) xs ts) = ts"
  by (induction xs arbitrary: ts) (auto simp: length_Suc_conv)

lemma finite_rows_map_values: "map2 (\<lambda>z t. (t,r z)) xs (map g xs) = map (\<lambda>z. (g z,r z)) xs"
  by (induction xs) auto

subsection \<open>The match of two clauses\<close>

definition finite_schema_match ::
  "('a,'s::linorder,'d) finite_factor_schema \<Rightarrow> ('b,'t::linorder,'d) finite_factor_schema \<Rightarrow>
    (('a \<Rightarrow> 'b) \<times> ('s \<Rightarrow> 't)) option" where
  "finite_schema_match S T =
    (case finite_rename_match [] (finite_schema_conclusion S) (finite_schema_conclusion T) of None \<Rightarrow> None
     | Some F \<Rightarrow> (case finite_rename_match_rows F (finite_schema_rows S) (finite_schema_rows T) of None \<Rightarrow> None
       | Some (G,ts) \<Rightarrow> Some (\<lambda>a. the (map_of G a),
           \<lambda>s. the (map_of (zip (map fst (finite_schema_rows S)) ts) s))))"

lemma finite_schema_rows_image:
  assumes formed: "finite_schema_formed S" "finite_schema_formed T"
    and image: "set (finite_schema_rows T) = (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ` set (finite_schema_rows S)"
    and conclusion: "finite_schema_conclusion T = map_finite_term_pattern f (finite_schema_conclusion S)"
  shows "T = finite_rename_schema f h id S"
proof -
  have calls: "fset (finite_schema_premises T) =
      (\<lambda>c. (h (fst c),fst (snd c),map_finite_term_pattern f (snd (snd c)))) ` fset (finite_schema_premises S)"
  proof (rule set_eqI, rule iffI)
    fix c
    assume target: "c \<in> fset (finite_schema_premises T)"
    obtain t c1 where c: "c = (t,c1)" by (cases c)
    have "(t,Inl c1) \<in> set (finite_schema_rows T)" using finite_schema_rows_member(1)[OF formed(2)] target c by simp
    then obtain z where z: "z \<in> set (finite_schema_rows S)" "t = h (fst z)"
      "Inl c1 = finite_rename_premise f (snd z)" using image by auto
    obtain s x where zz: "z = (s,x)" by (cases z)
    obtain c2 where x: "x = Inl c2" using z(3) zz by (cases x) auto
    have field_values: "c1 = (fst c2,map_finite_term_pattern f (snd c2))" using z(3) zz x by simp
    have source: "(s,c2) |\<in>| finite_schema_premises S" using finite_schema_rows_member(1)[OF formed(1)] z(1) zz x by simp
    show "c \<in> (\<lambda>c. (h (fst c),fst (snd c),map_finite_term_pattern f (snd (snd c)))) ` fset (finite_schema_premises S)"
      by (rule rev_image_eqI[OF source]) (simp add: c field_values z(2) zz)
  next
    fix c
    assume "c \<in> (\<lambda>c. (h (fst c),fst (snd c),map_finite_term_pattern f (snd (snd c)))) ` fset (finite_schema_premises S)"
    then obtain c0 where source: "c0 |\<in>| finite_schema_premises S"
      and c: "c = (h (fst c0),fst (snd c0),map_finite_term_pattern f (snd (snd c0)))" by auto
    have "(fst c0,Inl (snd c0)) \<in> set (finite_schema_rows S)"
      using finite_schema_rows_member(1)[OF formed(1)] source by simp
    then have "(h (fst c0),finite_rename_premise f (Inl (snd c0))) \<in> set (finite_schema_rows T)"
      using image by force
    then show "c \<in> fset (finite_schema_premises T)"
      using finite_schema_rows_member(1)[OF formed(2)] by (simp add: c)
  qed
  have materials: "fset (finite_schema_materials T) =
      (\<lambda>c. (h (fst c),finite_rename_material f (snd c))) ` fset (finite_schema_materials S)"
  proof (rule set_eqI, rule iffI)
    fix c
    assume target: "c \<in> fset (finite_schema_materials T)"
    obtain t N where c: "c = (t,N)" by (cases c)
    have "(t,Inr N) \<in> set (finite_schema_rows T)" using finite_schema_rows_member(2)[OF formed(2)] target c by simp
    then obtain z where z: "z \<in> set (finite_schema_rows S)" "t = h (fst z)"
      "Inr N = finite_rename_premise f (snd z)" using image by auto
    obtain s x where zz: "z = (s,x)" by (cases z)
    obtain M where x: "x = Inr M" using z(3) zz by (cases x) auto
    have field_values: "N = finite_rename_material f M" using z(3) zz x by simp
    have source: "(s,M) |\<in>| finite_schema_materials S" using finite_schema_rows_member(2)[OF formed(1)] z(1) zz x by simp
    show "c \<in> (\<lambda>c. (h (fst c),finite_rename_material f (snd c))) ` fset (finite_schema_materials S)"
      by (rule rev_image_eqI[OF source]) (simp add: c field_values z(2) zz)
  next
    fix c
    assume "c \<in> (\<lambda>c. (h (fst c),finite_rename_material f (snd c))) ` fset (finite_schema_materials S)"
    then obtain c0 where source: "c0 |\<in>| finite_schema_materials S"
      and c: "c = (h (fst c0),finite_rename_material f (snd c0))" by auto
    have "(fst c0,Inr (snd c0)) \<in> set (finite_schema_rows S)"
      using finite_schema_rows_member(2)[OF formed(1)] source by simp
    then have "(h (fst c0),finite_rename_premise f (Inr (snd c0))) \<in> set (finite_schema_rows T)"
      using image by force
    then show "c \<in> fset (finite_schema_materials T)"
      using finite_schema_rows_member(2)[OF formed(2)] by (simp add: c)
  qed
  show ?thesis
    by (rule finite_factor_schema.equality)
      (simp_all add: finite_rename_schema_def conclusion fset_inject[symmetric] fimage.rep_eq calls materials
        case_prod_unfold)
qed

theorem finite_schema_match_sound:
  assumes match: "finite_schema_match S T = Some (f,h)"
    and formed: "finite_schema_formed S" "finite_schema_formed T"
  shows "inj_on f (schema_variables (decode_finite_schema S)) \<and>
    inj_on h (schema_sockets (decode_finite_schema S)) \<and> T = finite_rename_schema f h id S"
proof -
  let ?xs = "finite_schema_rows S" and ?ys = "finite_schema_rows T"
  obtain F where head: "finite_rename_match [] (finite_schema_conclusion S) (finite_schema_conclusion T) = Some F"
    using match by (auto simp: finite_schema_match_def split: option.splits)
  obtain G ts where rows: "finite_rename_match_rows F ?xs ?ys = Some (G,ts)"
    and binder_map: "f = (\<lambda>a. the (map_of G a))"
    and socket_map: "h = (\<lambda>s. the (map_of (zip (map fst ?xs) ts) s))"
    using match head by (auto simp: finite_schema_match_def split: option.splits)
  note H = finite_rename_match_sound[OF head finite_injective_graph_empty]
  note B = finite_rename_match_rows_sound[OF rows conjunct1[OF H]]
  have keys: "distinct (map fst G)" using B by (simp add: finite_injective_graph_def)
  have conclusion: "finite_schema_conclusion T = map_finite_term_pattern f (finite_schema_conclusion S)"
  proof -
    have "set F \<subseteq> set G" using B by blast
    then show ?thesis using H keys by (simp add: binder_map)
  qed
  have length: "length ts = length ?xs" using B by blast
  have multiset: "mset ?ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs ts)"
    using B keys by (simp add: binder_map)
  have listed: "map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs ts =
      map (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ?xs"
    unfolding socket_map by (rule finite_rows_zip_values[OF length finite_schema_rows_keys(1)[OF formed(1)]])
  have image: "set ?ys = (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ` set ?xs"
    using mset_eq_setD[OF multiset] by (simp add: listed)
  have renamed: "T = finite_rename_schema f h id S"
    by (rule finite_schema_rows_image[OF formed image conclusion])
  have scope: "schema_variables (decode_finite_schema S) \<subseteq> fst ` set G"
  proof -
    have "fst ` set F \<subseteq> fst ` set G" using B by (simp add: image_mono)
    then show ?thesis using H B by (auto simp: finite_schema_rows_variables[OF formed(1)])
  qed
  have binders: "inj_on f (schema_variables (decode_finite_schema S))"
    unfolding binder_map by (rule inj_on_subset[OF finite_injective_graph_inj scope]) (use B in blast)
  have targets: "distinct ts"
  proof -
    have zip_keys: "map fst (map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs ts) = ts"
      by (rule finite_rows_zip_keys[OF length])
    have "mset (map fst ?ys) = image_mset fst (mset ?ys)" by (rule mset_map)
    also have "\<dots> = image_mset fst (mset (map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs ts))"
      by (simp only: multiset)
    also have "\<dots> = mset (map fst (map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs ts))"
      by (rule mset_map[symmetric])
    also have "\<dots> = mset ts" by (simp only: zip_keys)
    finally have same: "mset (map fst ?ys) = mset ts" .
    have "card (set ts) = length ts"
      using distinct_card[OF finite_schema_rows_keys(1)[OF formed(2)]] mset_eq_setD[OF same] mset_eq_length[OF same]
      by simp
    then show ?thesis by (rule card_distinct)
  qed
  have socket_graph: "finite_injective_graph (zip (map fst ?xs) ts)"
    using finite_schema_rows_keys(1)[OF formed(1)] targets length by (simp add: finite_injective_graph_def)
  have socket_keys: "fst ` set (zip (map fst ?xs) ts) = schema_sockets (decode_finite_schema S)"
  proof -
    have "fst ` set (zip (map fst ?xs) ts) = set (map fst (zip (map fst ?xs) ts))" by simp
    also have "\<dots> = set (map fst ?xs)" using length by simp
    finally show ?thesis using finite_schema_rows_keys(2)[OF formed(1)] by simp
  qed
  have sockets: "inj_on h (schema_sockets (decode_finite_schema S))"
    using finite_injective_graph_inj[OF socket_graph] by (simp only: socket_map socket_keys)
  show ?thesis using binders sockets renamed by blast
qed

theorem finite_schema_match_complete:
  assumes formed: "finite_schema_formed S" "finite_schema_formed T"
    and variant: "schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
  shows "finite_schema_match S T \<noteq> None"
proof -
  let ?xs = "finite_schema_rows S" and ?ys = "finite_schema_rows T"
  obtain f h where binders: "inj_on f (schema_variables (decode_finite_schema S))"
    and sockets: "inj_on h (schema_sockets (decode_finite_schema S))"
    and decoded: "decode_finite_schema T = rename_schema f h id (decode_finite_schema S)"
    using variant by (auto simp: schema_alpha_variant_def)
  have "decode_finite_schema T = decode_finite_schema (finite_rename_schema f h id S)"
    using decoded by (simp only: finite_rename_schema_correct)
  then have renamed: "T = finite_rename_schema f h id S" by (simp only: decode_finite_schema_injective)
  have scope: "schema_variables (decode_finite_schema S) = fset (finite_pattern_variables (finite_schema_conclusion S)) \<union>
      (\<Union>z\<in>set ?xs. fset (finite_premise_form_variables (snd z)))"
    by (rule finite_schema_rows_variables[OF formed(1)])
  have head_scope: "inj_on f (fst ` set [] \<union> fset (finite_pattern_variables (finite_schema_conclusion S)))"
    by (rule inj_on_subset[OF binders]) (simp add: scope)
  obtain F where head: "finite_rename_match [] (finite_schema_conclusion S)
      (map_finite_term_pattern f (finite_schema_conclusion S)) = Some F"
    and agree: "\<forall>z\<in>set F. f (fst z) = snd z"
    and domain: "fst ` set F = fst ` set [] \<union> fset (finite_pattern_variables (finite_schema_conclusion S))"
    using finite_rename_match_complete[OF head_scope] by auto
  have graph: "finite_injective_graph F"
    using finite_rename_match_sound[OF head finite_injective_graph_empty] by blast
  have conclusion: "finite_schema_conclusion T = map_finite_term_pattern f (finite_schema_conclusion S)"
    by (simp add: renamed finite_rename_schema_def)
  have target_rows: "set ?ys = (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ` set ?xs"
  proof -
    have "set ?ys = (\<lambda>z. (fst z,Inl (snd z))) ` fset (finite_schema_premises T) \<union>
        (\<lambda>z. (fst z,Inr (snd z))) ` fset (finite_schema_materials T)"
      by (rule finite_schema_rows_set[OF formed(2)])
    also have "\<dots> = (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) `
        ((\<lambda>z. (fst z,Inl (snd z))) ` fset (finite_schema_premises S) \<union>
         (\<lambda>z. (fst z,Inr (snd z))) ` fset (finite_schema_materials S))"
      by (simp add: renamed finite_rename_schema_def fimage.rep_eq image_image image_Un case_prod_unfold)
    also have "\<dots> = (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ` set ?xs"
      by (simp add: finite_schema_rows_set[OF formed(1)])
    finally show ?thesis .
  qed
  have source_keys: "distinct (map fst ?xs)" by (rule finite_schema_rows_keys(1)[OF formed(1)])
  have socket_scope: "inj_on h (set (map fst ?xs))"
    using sockets finite_schema_rows_keys(2)[OF formed(1)] by simp
  have distinct_image: "distinct (map (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ?xs)"
  proof -
    have "distinct (map h (map fst ?xs))"
      by (rule distinct_map[THEN iffD2]) (use source_keys socket_scope in blast)
    then have "distinct (map fst (map (\<lambda>z. (h (fst z),finite_rename_premise f (snd z))) ?xs))"
      by (simp add: comp_def)
    then show ?thesis by (auto simp: distinct_map intro: inj_on_imageI2)
  qed
  have distinct_rows: "distinct ?ys"
    using finite_schema_rows_keys(1)[OF formed(2)] by (simp add: distinct_map)
  have multiset: "mset ?ys = mset (map2 (\<lambda>z t. (t,finite_rename_premise f (snd z))) ?xs (map (\<lambda>z. h (fst z)) ?xs))"
    using set_eq_iff_mset_eq_distinct[OF distinct_rows distinct_image] target_rows
    by (simp add: finite_rows_map_values)
  have rows_scope: "inj_on f (fst ` set F \<union> (\<Union>z\<in>set ?xs. fset (finite_premise_form_variables (snd z))))"
    by (rule inj_on_subset[OF binders]) (auto simp: scope domain)
  have rows: "finite_rename_match_rows F ?xs ?ys \<noteq> None"
    by (rule finite_rename_match_rows_complete[OF rows_scope agree graph _ multiset]) simp
  show ?thesis using head rows by (auto simp: finite_schema_match_def conclusion split: option.splits)
qed

theorem finite_schema_match_exact:
  assumes "finite_schema_formed S" "finite_schema_formed T"
  shows "finite_schema_match S T = Some (f,h) \<Longrightarrow> inj_on f (schema_variables (decode_finite_schema S)) \<and>
      inj_on h (schema_sockets (decode_finite_schema S)) \<and> T = finite_rename_schema f h id S"
    and "finite_schema_match S T \<noteq> None \<longleftrightarrow> schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
proof -
  show "finite_schema_match S T = Some (f,h) \<Longrightarrow> inj_on f (schema_variables (decode_finite_schema S)) \<and>
      inj_on h (schema_sockets (decode_finite_schema S)) \<and> T = finite_rename_schema f h id S"
    using finite_schema_match_sound assms by blast
  show "finite_schema_match S T \<noteq> None \<longleftrightarrow> schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
  proof
    assume "finite_schema_match S T \<noteq> None"
    then obtain f' h' where "finite_schema_match S T = Some (f',h')" by auto
    note found = finite_schema_match_sound[OF this assms]
    show "schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
      unfolding schema_alpha_variant_def
      by (rule exI[of _ f'], rule exI[of _ h']) (use found in \<open>simp add: finite_rename_schema_correct\<close>)
  next
    assume "schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
    then show "finite_schema_match S T \<noteq> None" by (rule finite_schema_match_complete[OF assms])
  qed
qed

section \<open>The clause facts along a match\<close>

text \<open>
  A match of two formed clauses gives maps under which each premise of the first stands at the image of its socket
  in the second, holding the images of its variables, and every premise of the second is such an image; the
  conclusions correspond likewise. The rule instances of the two clauses are the same, instances and material
  checks correspond through the binder map and back through its inverse on the scope, and bindings carried there
  and back cancel, their bound values unchanged. These are facts over the two clauses alone, stated once for every
  reading that carries a clause's readings along its alpha variance.
\<close>


lemma finite_material_variables_rename:
  "finite_material_variables (finite_rename_material f M) = fimage f (finite_material_variables M)"
  by (rule fset_inject[THEN iffD1])
    (auto simp: finite_material_variables_def finite_rename_material_def finite_pattern_variables_map
      sup_fset.rep_eq fimage.rep_eq)

lemma finite_rename_schema_premise_member:
  "(t,e,q) |\<in>| finite_schema_premises (finite_rename_schema f h g S) \<longleftrightarrow>
    (\<exists>s d p. (s,d,p) |\<in>| finite_schema_premises S \<and> t = h s \<and> e = g d \<and> q = map_finite_term_pattern f p)"
proof
  assume "(t,e,q) |\<in>| finite_schema_premises (finite_rename_schema f h g S)"
  then have "(t,e,q) \<in> (\<lambda>(s,d,p). (h s,g d,map_finite_term_pattern f p)) ` fset (finite_schema_premises S)"
    by (simp add: finite_rename_schema_def fimage.rep_eq)
  then obtain c where c: "c \<in> fset (finite_schema_premises S)"
    and eq: "(t,e,q) = (\<lambda>(s,d,p). (h s,g d,map_finite_term_pattern f p)) c" by (rule imageE)
  obtain s d p where shape: "c = (s,d,p)" by (cases c) auto
  show "\<exists>s d p. (s,d,p) |\<in>| finite_schema_premises S \<and> t = h s \<and> e = g d \<and> q = map_finite_term_pattern f p"
    using c eq by (intro exI[of _ s] exI[of _ d] exI[of _ p]) (simp add: shape)
next
  assume "\<exists>s d p. (s,d,p) |\<in>| finite_schema_premises S \<and> t = h s \<and> e = g d \<and> q = map_finite_term_pattern f p"
  then obtain s d p where member: "(s,d,p) \<in> fset (finite_schema_premises S)"
    and eq: "t = h s" "e = g d" "q = map_finite_term_pattern f p" by blast
  have "(t,e,q) \<in> (\<lambda>(s,d,p). (h s,g d,map_finite_term_pattern f p)) ` fset (finite_schema_premises S)"
    by (rule rev_image_eqI[OF member]) (simp add: eq)
  then show "(t,e,q) |\<in>| finite_schema_premises (finite_rename_schema f h g S)"
    by (simp add: finite_rename_schema_def fimage.rep_eq)
qed

lemma finite_rename_schema_material_member:
  "(t,N) |\<in>| finite_schema_materials (finite_rename_schema f h g S) \<longleftrightarrow>
    (\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and> t = h s \<and> N = finite_rename_material f M)"
proof
  assume "(t,N) |\<in>| finite_schema_materials (finite_rename_schema f h g S)"
  then have "(t,N) \<in> (\<lambda>(s,M). (h s,finite_rename_material f M)) ` fset (finite_schema_materials S)"
    by (simp add: finite_rename_schema_def fimage.rep_eq)
  then obtain c where c: "c \<in> fset (finite_schema_materials S)"
    and eq: "(t,N) = (\<lambda>(s,M). (h s,finite_rename_material f M)) c" by (rule imageE)
  obtain s M where shape: "c = (s,M)" by (cases c) auto
  show "\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and> t = h s \<and> N = finite_rename_material f M"
    using c eq by (intro exI[of _ s] exI[of _ M]) (simp add: shape)
next
  assume "\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and> t = h s \<and> N = finite_rename_material f M"
  then obtain s M where member: "(s,M) \<in> fset (finite_schema_materials S)"
    and eq: "t = h s" "N = finite_rename_material f M" by blast
  have "(t,N) \<in> (\<lambda>(s,M). (h s,finite_rename_material f M)) ` fset (finite_schema_materials S)"
    by (rule rev_image_eqI[OF member]) (simp add: eq)
  then show "(t,N) |\<in>| finite_schema_materials (finite_rename_schema f h g S)"
    by (simp add: finite_rename_schema_def fimage.rep_eq)
qed

locale finite_schema_matched =
  fixes S :: "('a,'s::linorder,'d) finite_factor_schema" and T :: "('b,'t::linorder,'d) finite_factor_schema"
    and f :: "'a \<Rightarrow> 'b" and h :: "'s \<Rightarrow> 't"
  assumes source_formed: "finite_schema_formed S" and target_formed: "finite_schema_formed T"
    and matched: "finite_schema_match S T = Some (f,h)"
begin

lemma binders: "inj_on f (schema_variables (decode_finite_schema S))"
  and sockets: "inj_on h (schema_sockets (decode_finite_schema S))"
  and renamed: "T = finite_rename_schema f h id S"
  using finite_schema_match_exact(1)[OF source_formed target_formed matched] by blast+

lemma decoded: "decode_finite_schema T = rename_schema f h id (decode_finite_schema S)"
  by (simp only: renamed finite_rename_schema_correct)

lemma variant: "schema_alpha_variant (decode_finite_schema S) (decode_finite_schema T)"
  unfolding schema_alpha_variant_def using binders sockets decoded by blast

lemma target_variables: "schema_variables (decode_finite_schema T) = f ` schema_variables (decode_finite_schema S)"
  by (simp only: decoded renamed_schema_variables)

lemma target_sockets: "schema_sockets (decode_finite_schema T) = h ` schema_sockets (decode_finite_schema S)"
  by (simp only: decoded renamed_schema_sockets)

definition binder_inverse :: "'b \<Rightarrow> 'a" where
  "binder_inverse = inv_into (schema_variables (decode_finite_schema S)) f"

definition socket_inverse :: "'t \<Rightarrow> 's" where
  "socket_inverse = inv_into (schema_sockets (decode_finite_schema S)) h"

lemma inverse_binders: "inj_on binder_inverse (schema_variables (decode_finite_schema T))"
  unfolding binder_inverse_def target_variables by (rule inj_on_inv_into) simp

lemma inverse_sockets: "inj_on socket_inverse (schema_sockets (decode_finite_schema T))"
  unfolding socket_inverse_def target_sockets by (rule inj_on_inv_into) simp

lemma inverse_decoded: "decode_finite_schema S = rename_schema binder_inverse socket_inverse id (decode_finite_schema T)"
proof -
  have cancel: "rename_schema binder_inverse socket_inverse id (rename_schema f h id (decode_finite_schema S)) =
      decode_finite_schema S"
    by (rule rename_schema_cancels)
      (simp_all add: binder_inverse_def socket_inverse_def inv_into_f_f[OF binders] inv_into_f_f[OF sockets])
  show ?thesis by (simp only: decoded cancel)
qed

lemma inverse: "S = finite_rename_schema binder_inverse socket_inverse id T"
proof -
  have "decode_finite_schema S = decode_finite_schema (finite_rename_schema binder_inverse socket_inverse id T)"
    by (simp only: finite_rename_schema_correct inverse_decoded[symmetric])
  then show ?thesis by (simp only: decode_finite_schema_injective)
qed

lemma inverse_variant: "schema_alpha_variant (decode_finite_schema T) (decode_finite_schema S)"
  unfolding schema_alpha_variant_def using inverse_binders inverse_sockets inverse_decoded by blast

lemma source_socket:
  "(s,c) |\<in>| finite_schema_premises S \<Longrightarrow> s \<in> schema_sockets (decode_finite_schema S)"
  "(s,M) |\<in>| finite_schema_materials S \<Longrightarrow> s \<in> schema_sockets (decode_finite_schema S)"
  unfolding finite_schema_sockets_decoded by (metis Un_iff fst_conv image_eqI)+

lemma head_scope:
  "fset (finite_pattern_variables (finite_schema_conclusion S)) \<subseteq> schema_variables (decode_finite_schema S)"
  by (simp add: finite_schema_rows_variables[OF source_formed])

lemma call_scope:
  assumes "(s,d,p) |\<in>| finite_schema_premises S"
  shows "fset (finite_pattern_variables p) \<subseteq> schema_variables (decode_finite_schema S)"
proof -
  have "(s,Inl (d,p)) \<in> set (finite_schema_rows S)"
    using finite_schema_rows_member(1)[OF source_formed] assms by simp
  then have "fset (finite_premise_form_variables (snd (s,Inl (d,p)))) \<subseteq>
      (\<Union>z\<in>set (finite_schema_rows S). fset (finite_premise_form_variables (snd z)))"
    by (rule UN_upper[where B="\<lambda>z. fset (finite_premise_form_variables (snd z))"])
  note sub = this
  show ?thesis unfolding finite_schema_rows_variables[OF source_formed] by (rule le_supI2) (use sub in simp)
qed

lemma material_scope:
  assumes "(s,M) |\<in>| finite_schema_materials S"
  shows "fset (finite_material_variables M) \<subseteq> schema_variables (decode_finite_schema S)"
proof -
  have "(s,Inr M) \<in> set (finite_schema_rows S)"
    using finite_schema_rows_member(2)[OF source_formed] assms by simp
  then have "fset (finite_premise_form_variables (snd (s,Inr M :: ('a,'d) finite_premise_form))) \<subseteq>
      (\<Union>z\<in>set (finite_schema_rows S). fset (finite_premise_form_variables (snd z)))"
    by (rule UN_upper[where B="\<lambda>z. fset (finite_premise_form_variables (snd z))"])
  note sub = this
  show ?thesis unfolding finite_schema_rows_variables[OF source_formed] by (rule le_supI2) (use sub in simp)
qed

lemma conclusion: "finite_schema_conclusion T = map_finite_term_pattern f (finite_schema_conclusion S)"
  by (simp add: renamed finite_rename_schema_def)

lemma conclusion_variable:
  assumes "a \<in> schema_variables (decode_finite_schema S)"
  shows "f a |\<in>| finite_pattern_variables (finite_schema_conclusion T) \<longleftrightarrow>
    a |\<in>| finite_pattern_variables (finite_schema_conclusion S)"
  using inj_on_image_mem_iff[OF binders assms head_scope]
  by (simp add: conclusion finite_pattern_variables_map fimage.rep_eq)

lemma call:
  assumes "(s,d,p) |\<in>| finite_schema_premises S"
  shows "(h s,d,map_finite_term_pattern f p) |\<in>| finite_schema_premises T"
proof -
  have "\<exists>s' d' p'. (s',d',p') |\<in>| finite_schema_premises S \<and> h s = h s' \<and> d = id d' \<and>
      map_finite_term_pattern f p = map_finite_term_pattern f p'" using assms by auto
  then show ?thesis by (simp only: renamed finite_rename_schema_premise_member)
qed

lemma call_origin:
  assumes "(t,e,q) |\<in>| finite_schema_premises T"
  shows "\<exists>s p. (s,e,p) |\<in>| finite_schema_premises S \<and> t = h s \<and> q = map_finite_term_pattern f p"
proof -
  have "\<exists>s d p. (s,d,p) |\<in>| finite_schema_premises S \<and> t = h s \<and> e = id d \<and> q = map_finite_term_pattern f p"
    using assms by (simp only: renamed finite_rename_schema_premise_member)
  then show ?thesis by auto
qed

lemma call_at:
  assumes source: "(s,d,p) |\<in>| finite_schema_premises S"
  shows "(h s,e,q) |\<in>| finite_schema_premises T \<longleftrightarrow> e = d \<and> q = map_finite_term_pattern f p"
proof
  assume "(h s,e,q) |\<in>| finite_schema_premises T"
  then obtain s' p' where origin: "(s',e,p') |\<in>| finite_schema_premises S" "h s = h s'"
    "q = map_finite_term_pattern f p'" using call_origin by blast
  have same: "s = s'" by (rule inj_onD[OF sockets origin(2) source_socket(1)[OF source] source_socket(1)[OF origin(1)]])
  have functional: "single_valued (fset (finite_schema_premises S))"
    using source_formed by (simp add: finite_schema_formed_def finite_relation_functional_correct)
  have "(d,p) = (e,p')"
    by (rule single_valued_outputs[OF functional]) (use source origin(1) same in simp_all)
  then show "e = d \<and> q = map_finite_term_pattern f p" using origin(3) by simp
next
  assume "e = d \<and> q = map_finite_term_pattern f p"
  then show "(h s,e,q) |\<in>| finite_schema_premises T" using call[OF source] by simp
qed

lemma call_variable:
  assumes "(s,d,p) |\<in>| finite_schema_premises S" "a \<in> schema_variables (decode_finite_schema S)"
  shows "f a |\<in>| finite_pattern_variables (map_finite_term_pattern f p) \<longleftrightarrow> a |\<in>| finite_pattern_variables p"
  using inj_on_image_mem_iff[OF binders assms(2) call_scope[OF assms(1)]]
  by (simp add: finite_pattern_variables_map fimage.rep_eq)

lemma material:
  assumes "(s,M) |\<in>| finite_schema_materials S"
  shows "(h s,finite_rename_material f M) |\<in>| finite_schema_materials T"
proof -
  have "\<exists>s' M'. (s',M') |\<in>| finite_schema_materials S \<and> h s = h s' \<and>
      finite_rename_material f M = finite_rename_material f M'" using assms by auto
  then show ?thesis by (simp only: renamed finite_rename_schema_material_member)
qed

lemma material_origin:
  assumes "(t,N) |\<in>| finite_schema_materials T"
  shows "\<exists>s M. (s,M) |\<in>| finite_schema_materials S \<and> t = h s \<and> N = finite_rename_material f M"
  using assms by (simp only: renamed finite_rename_schema_material_member)

lemma material_at:
  assumes source: "(s,M) |\<in>| finite_schema_materials S"
  shows "(h s,N) |\<in>| finite_schema_materials T \<longleftrightarrow> N = finite_rename_material f M"
proof
  assume "(h s,N) |\<in>| finite_schema_materials T"
  then obtain s' M' where origin: "(s',M') |\<in>| finite_schema_materials S" "h s = h s'"
    "N = finite_rename_material f M'" using material_origin by blast
  have same: "s = s'" by (rule inj_onD[OF sockets origin(2) source_socket(2)[OF source] source_socket(2)[OF origin(1)]])
  have functional: "single_valued (fset (finite_schema_materials S))"
    using source_formed by (simp add: finite_schema_formed_def finite_relation_functional_correct)
  have "M = M'" by (rule single_valued_outputs[OF functional]) (use source origin(1) same in simp_all)
  then show "N = finite_rename_material f M" using origin(3) by simp
next
  assume "N = finite_rename_material f M"
  then show "(h s,N) |\<in>| finite_schema_materials T" using material[OF source] by simp
qed

lemma material_variable:
  assumes "(s,M) |\<in>| finite_schema_materials S" "a \<in> schema_variables (decode_finite_schema S)"
  shows "f a |\<in>| finite_material_variables (finite_rename_material f M) \<longleftrightarrow> a |\<in>| finite_material_variables M"
  using inj_on_image_mem_iff[OF binders assms(2) material_scope[OF assms(1)]]
  by (simp add: finite_material_variables_rename fimage.rep_eq)

lemma forward_instance:
  assumes "schema_instance (decode_finite_schema S) V t Q"
  shows "schema_instance (decode_finite_schema T) (rename_term_bindings f V) t (map_socket_graph h id id Q)"
  using schema_instance_renaming[where g=id, OF assms binders sockets] by (simp only: decoded)

lemma backward_instance:
  assumes "schema_instance (decode_finite_schema T) W t R"
  shows "schema_instance (decode_finite_schema S) (rename_term_bindings binder_inverse W) t
    (map_socket_graph socket_inverse id id R)"
  using schema_instance_renaming[where g=id, OF assms inverse_binders inverse_sockets]
  by (simp only: inverse_decoded[symmetric])

lemma material_satisfied:
  assumes "term_bindings_formed (schema_variables (decode_finite_schema S)) V"
  shows "schema_material_satisfied (decode_finite_schema T) (rename_term_bindings f V) \<longleftrightarrow>
    schema_material_satisfied (decode_finite_schema S) V"
  using schema_material_satisfied_renaming[where h=h and g=id, OF assms binders] by (simp only: decoded)

lemma rule_instances: "schema_rule_instance (decode_finite_schema T) X t \<longleftrightarrow> schema_rule_instance (decode_finite_schema S) X t"
  by (rule schema_alpha_rule_instance[OF variant])

lemma forward_bindings:
  assumes "term_bindings_formed (schema_variables (decode_finite_schema S)) V"
  shows "term_bindings_formed (schema_variables (decode_finite_schema T)) (rename_term_bindings f V)"
  using renamed_term_bindings_formed[OF assms binders] by (simp only: target_variables)

lemma backward_bindings:
  assumes "term_bindings_formed (schema_variables (decode_finite_schema T)) W"
  shows "term_bindings_formed (schema_variables (decode_finite_schema S)) (rename_term_bindings binder_inverse W)"
proof -
  have scope: "binder_inverse ` schema_variables (decode_finite_schema T) = schema_variables (decode_finite_schema S)"
    by (simp only: target_variables binder_inverse_def inv_into_image_cancel[OF binders order_refl])
  show ?thesis using renamed_term_bindings_formed[OF assms inverse_binders] by (simp only: scope)
qed

lemma bindings_cancel:
  assumes "term_bindings_formed (schema_variables (decode_finite_schema S)) V"
  shows "rename_term_bindings binder_inverse (rename_term_bindings f V) = V"
proof -
  have domain: "rel_dom V = schema_variables (decode_finite_schema S)"
    using assms by (simp add: term_bindings_formed_def)
  have restored: "binder_inverse (f (fst z)) = fst z" if "z \<in> V" for z
  proof -
    have "fst z \<in> schema_variables (decode_finite_schema S)" using that domain by (force simp: rel_dom_image)
    then show ?thesis by (simp add: binder_inverse_def inv_into_f_f[OF binders])
  qed
  have "rename_term_bindings binder_inverse (rename_term_bindings f V) =
      (\<lambda>z. (binder_inverse (f (fst z)),snd z)) ` V"
    by (simp add: rename_term_bindings_def image_image case_prod_unfold)
  also have "\<dots> = (\<lambda>z. z) ` V" by (rule image_cong[OF refl]) (simp add: restored prod_eq_iff)
  finally show ?thesis by simp
qed

lemma bindings_cancel_backward:
  assumes "term_bindings_formed (schema_variables (decode_finite_schema T)) W"
  shows "rename_term_bindings f (rename_term_bindings binder_inverse W) = W"
proof -
  have domain: "rel_dom W = f ` schema_variables (decode_finite_schema S)"
    using assms by (simp add: term_bindings_formed_def target_variables)
  have restored: "f (binder_inverse (fst z)) = fst z" if "z \<in> W" for z
  proof -
    have "fst z \<in> f ` schema_variables (decode_finite_schema S)" using that domain by (force simp: rel_dom_image)
    then show ?thesis by (simp add: binder_inverse_def f_inv_into_f)
  qed
  have "rename_term_bindings f (rename_term_bindings binder_inverse W) =
      (\<lambda>z. (f (binder_inverse (fst z)),snd z)) ` W"
    by (simp add: rename_term_bindings_def image_image case_prod_unfold)
  also have "\<dots> = (\<lambda>z. z) ` W" by (rule image_cong[OF refl]) (simp add: restored prod_eq_iff)
  finally show ?thesis by simp
qed

end

export_code finite_schema_match checking SML

end
