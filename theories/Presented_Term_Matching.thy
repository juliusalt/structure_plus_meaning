theory Presented_Term_Matching
  imports Factor_Constructed_Program_Applications Factor_Instantiated_Premises
begin

section \<open>A presentation of terms, passed as an argument\<close>

text \<open>
  An evaluator may hold its terms in another form than the plain terms it decodes them to. A
  presentation is passed to the operations below as the keyed operations take their key: its view, the
  top constructor of a presented term with presented components; its canonical constructors of a
  target leaf, a payload leaf and a pair; and its decoding to a plain term. Plain terms are the
  identity presentation.
\<close>

datatype 'p term_view = View_Target finite_exact_target | View_Payload octets | View_Pair 'p 'p

fun finite_term_view :: "finite_factor_term \<Rightarrow> finite_factor_term term_view" where
  "finite_term_view (Finite_Target x)=View_Target x"
| "finite_term_view (Finite_Payload v)=View_Payload v"
| "finite_term_view (Finite_Pair x y)=View_Pair x y"

lemma finite_term_view_target: "finite_term_view u=View_Target x \<longleftrightarrow> u=Finite_Target x"
  by (cases u) auto

lemma finite_term_view_payload: "finite_term_view u=View_Payload v \<longleftrightarrow> u=Finite_Payload v"
  by (cases u) auto

lemma finite_term_view_pair: "finite_term_view u=View_Pair x y \<longleftrightarrow> u=Finite_Pair x y"
  by (cases u) auto

record 'p term_presentation =
  presented_view :: "'p \<Rightarrow> 'p term_view"
  presented_target :: "finite_exact_target \<Rightarrow> 'p"
  presented_payload :: "octets \<Rightarrow> 'p"
  presented_pair :: "'p \<Rightarrow> 'p \<Rightarrow> 'p"
  presented_decode :: "'p \<Rightarrow> finite_factor_term"

text \<open>
  The obligations a presentation meets over a domain of presented terms: equality on the domain decides
  equality of the decoded terms; the constructors applied to domain members give domain members and
  commute with decoding, and the components the view gives of a domain member are domain members; the
  view commutes with decoding.
\<close>

locale presented_terms =
  fixes P :: "'p term_presentation" and D :: "'p set"
  assumes decides: "\<And>x y. x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow> presented_decode P x=presented_decode P y \<Longrightarrow> x=y"
    and target: "\<And>a. presented_target P a\<in>D"
      "\<And>a. presented_decode P (presented_target P a)=Finite_Target a"
    and payload: "\<And>v. presented_payload P v\<in>D"
      "\<And>v. presented_decode P (presented_payload P v)=Finite_Payload v"
    and pair: "\<And>x y. x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow> presented_pair P x y\<in>D"
      "\<And>x y. x\<in>D \<Longrightarrow> y\<in>D \<Longrightarrow>
        presented_decode P (presented_pair P x y)=Finite_Pair (presented_decode P x) (presented_decode P y)"
    and components: "\<And>x a b. x\<in>D \<Longrightarrow> presented_view P x=View_Pair a b \<Longrightarrow> a\<in>D \<and> b\<in>D"
    and view: "\<And>x. x\<in>D \<Longrightarrow>
      map_term_view (presented_decode P) (presented_view P x)=finite_term_view (presented_decode P x)"
begin

lemma view_target:
  assumes "x\<in>D" "presented_view P x=View_Target a"
  shows "presented_decode P x=Finite_Target a"
  using view[OF assms(1)] assms(2) by (cases "presented_decode P x") auto

lemma view_payload:
  assumes "x\<in>D" "presented_view P x=View_Payload v"
  shows "presented_decode P x=Finite_Payload v"
  using view[OF assms(1)] assms(2) by (cases "presented_decode P x") auto

lemma view_pair:
  assumes "x\<in>D" "presented_view P x=View_Pair a b"
  shows "presented_decode P x=Finite_Pair (presented_decode P a) (presented_decode P b) \<and> a\<in>D \<and> b\<in>D"
  using view[OF assms(1)] assms(2) components[OF assms] by (cases "presented_decode P x") auto

end

section \<open>Matching and instantiation over a presentation\<close>

text \<open>
  A literal leaf is fitted by comparing the presented term with the leaf the canonical constructor
  builds, and repeated occurrences of a variable are compared as presented terms: no term is decoded.
\<close>

fun presented_pattern_fits :: "'p term_presentation \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'p \<Rightarrow> bool" where
  "presented_pattern_fits P (Finite_Variable a) t=True"
| "presented_pattern_fits P (Finite_Pattern_Target x) t=(finite_target_formed x \<and> t=presented_target P x)"
| "presented_pattern_fits P (Finite_Pattern_Payload v) t=(octets_formed v \<and> t=presented_payload P v)"
| "presented_pattern_fits P (Finite_Pattern_Pair p q) t=(case presented_view P t of View_Pair x y \<Rightarrow>
    presented_pattern_fits P p x \<and> presented_pattern_fits P q y | _ \<Rightarrow> False)"

fun presented_matching_rows :: "'p term_presentation \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'p \<Rightarrow> ('a\<times>'p) list" where
  "presented_matching_rows P (Finite_Variable a) t=[(a,t)]"
| "presented_matching_rows P (Finite_Pattern_Target x) t=[]"
| "presented_matching_rows P (Finite_Pattern_Payload v) t=[]"
| "presented_matching_rows P (Finite_Pattern_Pair p q) t=(case presented_view P t of View_Pair x y \<Rightarrow>
    presented_matching_rows P p x@presented_matching_rows P q y | _ \<Rightarrow> [])"

definition presented_matching_bindings ::
    "'p term_presentation \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'p \<Rightarrow> ('a\<times>'p) fset" where
  "presented_matching_bindings P p t=fset_of_list (presented_matching_rows P p t)"

definition presented_matching_functional :: "'p term_presentation \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'p \<Rightarrow> bool" where
  "presented_matching_functional P p t=relation_rows_functional (presented_matching_rows P p t)"

fun presented_pattern_instances ::
    "'p term_presentation \<Rightarrow> ('a\<times>'p) fset \<Rightarrow> 'a finite_term_pattern \<Rightarrow> 'p fset" where
  "presented_pattern_instances P V (Finite_Variable a)=fimage snd (ffilter (\<lambda>x. fst x=a) V)"
| "presented_pattern_instances P V (Finite_Pattern_Target x)=
    (if finite_target_formed x then {|presented_target P x|} else {||})"
| "presented_pattern_instances P V (Finite_Pattern_Payload v)=
    (if octets_formed v then {|presented_payload P v|} else {||})"
| "presented_pattern_instances P V (Finite_Pattern_Pair p q)=
    ffUnion (fimage (\<lambda>x. fimage (presented_pair P x) (presented_pattern_instances P V q))
      (presented_pattern_instances P V p))"

definition presented_instantiated_premises :: "'p term_presentation \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow>
    ('a\<times>'p) fset \<Rightarrow> ('s\<times>('d\<times>'p)) fset" where
  "presented_instantiated_premises P S V=ffUnion (fimage (\<lambda>(s,d,p).
    fimage (\<lambda>t. (s,d,t)) (presented_pattern_instances P V p)) (finite_schema_premises S))"


section \<open>Every operation commutes with decoding, once for every presentation\<close>

context presented_terms
begin

theorem presented_pattern_fits_decode:
  "t\<in>D \<Longrightarrow> presented_pattern_fits P p t \<longleftrightarrow> finite_pattern_fits p (presented_decode P t)"
proof (induction p arbitrary: t)
  case (Finite_Variable a)
  then show ?case by simp
next
  case (Finite_Pattern_Target x)
  have "t=presented_target P x \<longleftrightarrow> presented_decode P t=Finite_Target x"
    using decides[of t "presented_target P x"] target Finite_Pattern_Target.prems by auto
  then show ?case by simp
next
  case (Finite_Pattern_Payload v)
  have "t=presented_payload P v \<longleftrightarrow> presented_decode P t=Finite_Payload v"
    using decides[of t "presented_payload P v"] payload Finite_Pattern_Payload.prems by auto
  then show ?case by simp
next
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases "presented_view P t")
    case (View_Target a)
    then show ?thesis using view_target[OF Finite_Pattern_Pair.prems View_Target] by simp
  next
    case (View_Payload v)
    then show ?thesis using view_payload[OF Finite_Pattern_Pair.prems View_Payload] by simp
  next
    case (View_Pair a b)
    then show ?thesis
      using view_pair[OF Finite_Pattern_Pair.prems View_Pair] Finite_Pattern_Pair.IH by simp
  qed
qed

lemma presented_matching_rows_domain:
  "t\<in>D \<Longrightarrow> snd ` set (presented_matching_rows P p t)\<subseteq>D"
proof (induction p arbitrary: t)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases "presented_view P t")
    case (View_Pair a b)
    then show ?thesis
      using view_pair[OF Finite_Pattern_Pair.prems View_Pair] Finite_Pattern_Pair.IH by (simp add: image_Un)
  qed simp_all
qed simp_all

theorem presented_matching_rows_decode:
  "t\<in>D \<Longrightarrow> map (map_prod id (presented_decode P)) (presented_matching_rows P p t)=
    finite_matching_rows p (presented_decode P t)"
proof (induction p arbitrary: t)
  case (Finite_Pattern_Pair p q)
  show ?case
  proof (cases "presented_view P t")
    case (View_Target a)
    then show ?thesis using view_target[OF Finite_Pattern_Pair.prems View_Target] by simp
  next
    case (View_Payload v)
    then show ?thesis using view_payload[OF Finite_Pattern_Pair.prems View_Payload] by simp
  next
    case (View_Pair a b)
    then show ?thesis
      using view_pair[OF Finite_Pattern_Pair.prems View_Pair] Finite_Pattern_Pair.IH by simp
  qed
qed simp_all

lemma presented_matching_bindings_domain:
  "t\<in>D \<Longrightarrow> snd ` fset (presented_matching_bindings P p t)\<subseteq>D"
  by (simp add: presented_matching_bindings_def fset_of_list.rep_eq presented_matching_rows_domain)

theorem presented_matching_bindings_decode:
  "t\<in>D \<Longrightarrow> fimage (map_prod id (presented_decode P)) (presented_matching_bindings P p t)=
    finite_matching_bindings p (presented_decode P t)"
  by (metis presented_matching_bindings_def finite_matching_rows_bindings presented_matching_rows_decode
      fset_of_list_map)

lemma rows_functional_decode:
  assumes bounded: "snd ` set xs\<subseteq>D"
  shows "relation_rows_functional (map (map_prod id (presented_decode P)) xs) \<longleftrightarrow> relation_rows_functional xs"
proof -
  have rows: "map_prod id (presented_decode P) ` set xs=map_relation_values (presented_decode P) (set xs)"
    by (simp add: map_relation_values_def map_prod_def)
  have "inj_on (presented_decode P) (rel_ran (set xs))"
    using bounded unfolding inj_on_def rel_ran_image by (blast intro: decides)
  then show ?thesis
    unfolding relation_rows_functional_exact list.set_map rows by (rule map_relation_values_functional_on)
qed

theorem presented_matching_functional_decode:
  "t\<in>D \<Longrightarrow> presented_matching_functional P p t \<longleftrightarrow> finite_matching_functional p (presented_decode P t)"
proof -
  assume t: "t\<in>D"
  have domain: "snd ` set (presented_matching_rows P p t)\<subseteq>D"
    by (rule presented_matching_rows_domain[OF t])
  have "presented_matching_functional P p t \<longleftrightarrow>
      relation_rows_functional (map (map_prod id (presented_decode P)) (presented_matching_rows P p t))"
    unfolding presented_matching_functional_def by (rule rows_functional_decode[OF domain, symmetric])
  also have "\<dots> \<longleftrightarrow> finite_matching_functional p (presented_decode P t)"
    by (simp add: finite_matching_functional_def presented_matching_rows_decode[OF t])
  finally show ?thesis .
qed

lemma presented_pattern_instances_domain:
  assumes V: "snd ` fset V\<subseteq>D"
  shows "fset (presented_pattern_instances P V p)\<subseteq>D"
proof (induction p)
  case (Finite_Pattern_Pair p q)
  then show ?case using pair(1) by (auto simp: fimage.rep_eq ffUnion.rep_eq)
qed (use V target payload in \<open>auto simp: fimage.rep_eq ffilter.rep_eq\<close>)

theorem presented_pattern_instances_decode:
  assumes V: "snd ` fset V\<subseteq>D"
  shows "fimage (presented_decode P) (presented_pattern_instances P V p)=
    finite_pattern_instances (fimage (map_prod id (presented_decode P)) V) p"
proof (induction p)
  case (Finite_Variable a)
  show ?case
    by (rule fset_inject[THEN iffD1]) (force simp: fimage.rep_eq ffilter.rep_eq)
next
  case (Finite_Pattern_Target x)
  then show ?case by (simp add: target)
next
  case (Finite_Pattern_Payload v)
  then show ?case by (simp add: payload)
next
  case (Finite_Pattern_Pair p q)
  have left: "fset (presented_pattern_instances P V p)\<subseteq>D"
    and right: "fset (presented_pattern_instances P V q)\<subseteq>D"
    using presented_pattern_instances_domain[OF V] by blast+
  have decoded: "presented_decode P (presented_pair P x y)=Finite_Pair (presented_decode P x) (presented_decode P y)"
    if "x\<in>fset (presented_pattern_instances P V p)" "y\<in>fset (presented_pattern_instances P V q)" for x y
    using pair(2) left right that by blast
  show ?case
    unfolding presented_pattern_instances.simps finite_pattern_instances.simps Finite_Pattern_Pair.IH[symmetric]
    by (rule fset_inject[THEN iffD1]) (force simp: fimage.rep_eq ffUnion.rep_eq decoded)
qed

theorem presented_instantiated_premises_decode:
  assumes V: "snd ` fset V\<subseteq>D"
  shows "fimage (\<lambda>(s,d,t). (s,d,presented_decode P t)) (presented_instantiated_premises P S V)=
    finite_instantiated_premises S (fimage (map_prod id (presented_decode P)) V)"
proof (rule fset_inject[THEN iffD1])
  have instances: "fset (finite_pattern_instances (fimage (map_prod id (presented_decode P)) V) p)=
      presented_decode P ` fset (presented_pattern_instances P V p)" for p
    by (simp add: fimage.rep_eq flip: presented_pattern_instances_decode[OF V])
  show "fset (fimage (\<lambda>(s,d,t). (s,d,presented_decode P t)) (presented_instantiated_premises P S V))=
      fset (finite_instantiated_premises S (fimage (map_prod id (presented_decode P)) V))"
    by (auto simp: presented_instantiated_premises_def finite_instantiated_premises_def fimage.rep_eq
        ffUnion.rep_eq instances split: prod.splits; force)
qed

end

section \<open>Plain terms are the identity presentation\<close>

definition plain_term_presentation :: "finite_factor_term term_presentation" where
  "plain_term_presentation=\<lparr>presented_view=finite_term_view, presented_target=Finite_Target,
    presented_payload=Finite_Payload, presented_pair=Finite_Pair, presented_decode=id\<rparr>"

lemma plain_term_presentation_fields [simp]:
  "presented_view plain_term_presentation=finite_term_view"
  "presented_target plain_term_presentation=Finite_Target"
  "presented_payload plain_term_presentation=Finite_Payload"
  "presented_pair plain_term_presentation=Finite_Pair"
  "presented_decode plain_term_presentation=id"
  by (simp_all add: plain_term_presentation_def)

interpretation plain_terms: presented_terms plain_term_presentation UNIV
  by unfold_locales (simp_all add: term_view.map_id)

text \<open>
  Each identity instance is the commutation proved once for every presentation, taken at the plain
  presentation, whose decoding is the identity: no operation is argued again.
\<close>

theorem plain_pattern_fits: "presented_pattern_fits plain_term_presentation p t \<longleftrightarrow> finite_pattern_fits p t"
  using plain_terms.presented_pattern_fits_decode[of t p] by simp

theorem plain_matching_rows: "presented_matching_rows plain_term_presentation p t=finite_matching_rows p t"
  using plain_terms.presented_matching_rows_decode[of t p] by (simp add: map_prod.id)

theorem plain_matching_bindings:
  "presented_matching_bindings plain_term_presentation p t=finite_matching_bindings p t"
  by (simp add: presented_matching_bindings_def plain_matching_rows finite_matching_rows_bindings)

theorem plain_matching_functional:
  "presented_matching_functional plain_term_presentation p t \<longleftrightarrow> finite_matching_functional p t"
  by (simp add: presented_matching_functional_def finite_matching_functional_def plain_matching_rows)

theorem plain_pattern_instances:
  "presented_pattern_instances plain_term_presentation V p=finite_pattern_instances V p"
  using plain_terms.presented_pattern_instances_decode[of V p] by (simp add: map_prod.id)

theorem plain_instantiated_premises:
  "presented_instantiated_premises plain_term_presentation S V=finite_instantiated_premises S V"
  by (simp add: presented_instantiated_premises_def finite_instantiated_premises_def plain_pattern_instances)

end
