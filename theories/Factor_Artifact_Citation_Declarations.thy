theory Factor_Artifact_Citation_Declarations
  imports Factor_Producer_Correspondences Factor_Resolution_Carriers Factor_Root_Family_Declarations Factor_Citation_Reading
    Factor_Headed_Material Factor_Artifact_Comparison Factor_Data_Collection_Operations
    Factor_Scoped_Instantiation Factor_Record_Admission Factor_Term_Sequence_Presentations
begin

text \<open>
  The artifacts' and citations' declarations (R6b of DECISIONS.md "The native evaluator constructs the missing
  witnesses by resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets"):
  artifact lookup (37), artifact identity (12) and comparison (7), headed material (29), citation admission (36) and
  reading (42), citation resolution (39) and interpretation (40) and binder admission (54) at their views, the
  consumers the clauses holding their outputs derive, and the sockets inside them, each discharged at its notion's own
  system from the notion's contract. The sites are the given's readers' own numbers; the records are read by the
  committed search alone, and no clause of any program changes.
\<close>

section \<open>The views\<close>

text \<open>
  Each view is a linear pattern of its site's argument and a pair over exactly its variables
  (@{const view_formed}). A view's term function is characterized by the shape it matches, each characterization the
  instance of @{thm [source] resolution_view_term_values} at the view's variables.
\<close>

text \<open>37's view: the environment and use are its input, the artifact its output.\<close>

definition lookup_view :: "nat resolution_view" where
  "lookup_view = (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),Finite_Variable 2)"

lemma lookup_view_formed: "view_formed lookup_view"
  by (auto simp: view_formed_def lookup_view_def fset_eq_iff)

lemma lookup_view_term:
  "resolution_view_term lookup_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>e u. t = Pair_Term e (Pair_Term u y) \<and> x = Pair_Term e u)"
  using resolution_view_term_values[OF lookup_view_formed[unfolded lookup_view_def], of 3 t x y]
  by (auto simp: lookup_view_def view_values_simps)

text \<open>36's and 40's view: the argument's first pair and its second pair's left are the input, its last field the output.\<close>

definition inner_right_view :: "nat resolution_view" where
  "inner_right_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),Finite_Variable 3)"

lemma inner_right_view_formed: "view_formed inner_right_view"
  by (auto simp: view_formed_def inner_right_view_def fset_eq_iff)

lemma inner_right_view_term:
  "resolution_view_term inner_right_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>a b c. t = Pair_Term (Pair_Term a b) (Pair_Term c y) \<and> x = Pair_Term (Pair_Term a b) c)"
  using resolution_view_term_values[OF inner_right_view_formed[unfolded inner_right_view_def], of 4 t x y]
  by (auto simp: inner_right_view_def view_values_simps)

text \<open>39's and 42's view: the last two fields are the output, 42 naming each a hole.\<close>

definition outer_pair_view :: "nat resolution_view" where
  "outer_pair_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))"

definition outer_pair_holes :: "nat finite_term_pattern list" where
  "outer_pair_holes = [Finite_Variable 3,Finite_Variable 4]"

lemma outer_pair_view_formed: "view_formed outer_pair_view"
  by (auto simp: view_formed_def outer_pair_view_def fset_eq_iff)

lemma outer_pair_view_term:
  "resolution_view_term outer_pair_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>a b c v w. t = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term v w)) \<and> x = Pair_Term (Pair_Term a b) c \<and>
      y = Pair_Term v w)"
  using resolution_view_term_values[OF outer_pair_view_formed[unfolded outer_pair_view_def], of 5 t x y]
  by (auto simp: outer_pair_view_def view_values_simps)

lemma outer_pair_view_holes:
  "resolution_view_holes outer_pair_view outer_pair_holes t = Some w \<longleftrightarrow>
    (\<exists>a b c v z. t = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term v z)) \<and> w = [v,z])"
  by (auto simp: resolution_view_holes_def outer_pair_view_def outer_pair_holes_def view_match_pair_some
    view_lookup_def split: option.splits)

text \<open>29's field view: the artifact and root are the input, the three collected fields its holes.\<close>

definition headed_fields_view :: "nat resolution_view" where
  "headed_fields_view = (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)))),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)))"

definition headed_fields_holes :: "nat finite_term_pattern list" where
  "headed_fields_holes = [Finite_Variable 2,Finite_Variable 3,Finite_Variable 4]"

lemma headed_fields_view_formed: "view_formed headed_fields_view"
  by (auto simp: view_formed_def headed_fields_view_def fset_eq_iff)

lemma headed_fields_view_term:
  "resolution_view_term headed_fields_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>a r e b f. t = headed_material_argument a r e b f \<and> x = Pair_Term a r \<and> y = Pair_Term e (Pair_Term b f))"
  using resolution_view_term_values[OF headed_fields_view_formed[unfolded headed_fields_view_def], of 5 t x y]
  by (auto simp: headed_fields_view_def view_values_simps)

lemma headed_fields_view_holes:
  "resolution_view_holes headed_fields_view headed_fields_holes t = Some w \<longleftrightarrow>
    (\<exists>a r e b f. t = headed_material_argument a r e b f \<and> w = [e,b,f])"
  by (auto simp: resolution_view_holes_def headed_fields_view_def headed_fields_holes_def view_match_pair_some
    view_lookup_def split: option.splits)

section \<open>The classes at the producers' outputs\<close>

text \<open>
  37's and 12's outputs present an artifact (R6's class at 10); 7's output is four collected fields, each a bag (R6's
  class at 6), and two correspond field by field; 29's three fields, 36's interior, 42's interior and 54's binders are
  bags; 42's citation is one value; 39's output is a use and a target presentation, the use one value; 40's is a
  target presentation (R6's class at 45).
\<close>

definition fields_correspondence :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "fields_correspondence y y' \<longleftrightarrow> (\<exists>a e b f a' e' b' f'. y = artifact_fields_term a e b f \<and>
    y' = artifact_fields_term a' e' b' f' \<and> given_correspondence 6 a a' \<and> given_correspondence 6 e e' \<and>
    given_correspondence 6 b b' \<and> given_correspondence 6 f f')"

definition resolved_correspondence :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "resolved_correspondence z z' \<longleftrightarrow> (\<exists>v y y'. z = Pair_Term v y \<and> z' = Pair_Term v y' \<and> given_correspondence 45 y y')"

definition artifact_citation_correspondence :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "artifact_citation_correspondence d i = (if d = 37 \<or> d = 12 then given_correspondence 10
    else if d = 7 then fields_correspondence
    else if d = 29 \<or> d = 36 \<or> d = 54 then given_correspondence 6
    else if d = 42 then (if i = 0 then (=) else given_correspondence 6)
    else if d = 39 then resolved_correspondence
    else if d = 40 then given_correspondence 45
    else given_correspondence d)"

lemma bag_correspondence_lists:
  assumes "data_elements xs" "data_elements ys" "mset xs = mset ys"
  shows "given_correspondence 6 (data_list_term xs) (data_list_term ys)"
  unfolding given_correspondence_def presentation_transport_def data_bag_value_presents_def
  using assms by (simp; blast)

lemma bag_answers_correspond:
  assumes "(6,Pair_Term x y) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x y') \<in> positive_meaning bag_comparison_system"
  shows "given_correspondence 6 y y'"
  using bag_producer_discharged assms unfolding producer_discharged_identity by blast

lemma artifact_correspondence_at:
  assumes "artifact_value_presents R y" "artifact_value_presents R y'"
  shows "given_correspondence 10 y y'"
  using assms by (auto simp: given_correspondence_def presentation_transport_def)

lemma target_correspondence_at:
  assumes "target_value_presents x y" "target_value_presents x y'"
  shows "given_correspondence 45 y y'"
  using assms by (auto simp: given_correspondence_def presentation_transport_def)

lemma payload_elements:
  assumes "term_formed (data_list_term (map Payload_Term xs))"
  shows "data_elements (map Payload_Term xs)"
  using assms by (auto simp: data_list_term_formed)

lemma distinct_payload_bags:
  assumes "term_formed (data_list_term (map Payload_Term xs))" "term_formed (data_list_term (map Payload_Term ys))"
    "distinct xs" "distinct ys" "set xs = set ys"
  shows "given_correspondence 6 (data_list_term (map Payload_Term xs)) (data_list_term (map Payload_Term ys))"
proof -
  have "mset xs = mset ys" using assms(3-5) by (simp add: set_eq_iff_mset_eq_distinct)
  then show ?thesis using bag_correspondence_lists payload_elements assms(1,2) by simp
qed

section \<open>Each producer discharged at its notion's system\<close>

theorem lookup_producer_discharged:
  "producer_discharged (positive_meaning artifact_lookup_system) 37 lookup_view [snd (snd lookup_view)]
    (artifact_citation_correspondence 37)"
  unfolding producer_discharged_single lookup_view_term
proof (intro allI impI)
  fix a b u v v'
  assume ha: "(37,a) \<in> positive_meaning artifact_lookup_system" and hb: "(37,b) \<in> positive_meaning artifact_lookup_system"
    and va: "\<exists>e w. a = Pair_Term e (Pair_Term w v) \<and> u = Pair_Term e w"
    and vb: "\<exists>e w. b = Pair_Term e (Pair_Term w v') \<and> u = Pair_Term e w"
  from va obtain e w where a: "a = Pair_Term e (Pair_Term w v)" and u: "u = Pair_Term e w" by blast
  from vb obtain e' w' where b: "b = Pair_Term e' (Pair_Term w' v')" and u': "u = Pair_Term e' w'" by blast
  have same: "e' = e" "w' = w" using u u' by simp_all
  obtain E q R where E: "environment_value_presents E e" and w: "w = use_data_term q"
    and at: "artifact_at E q R" and R: "artifact_value_presents R v"
    using ha a by (auto simp: artifact_lookup_exact)
  obtain E' q' R' where E': "environment_value_presents E' e" and w': "w = use_data_term q'"
    and at': "artifact_at E' q' R'" and R': "artifact_value_presents R' v'"
    using hb b same by (auto simp: artifact_lookup_exact)
  have "E' = E" using E E' environment_value_presents_unique by metis
  moreover have "q' = q" using w w' use_data_term_injective by (metis injD)
  ultimately have "R' = R" using at at' environment_artifact_unique environment_value_presents_formed E by metis
  then show "artifact_citation_correspondence 37 0 v v'"
    using artifact_correspondence_at R R' by (simp add: artifact_citation_correspondence_def)
qed

theorem identity_producer_discharged:
  "producer_discharged (positive_meaning artifact_identity_system) 12 view_identity [view_output]
    (artifact_citation_correspondence 12)"
  unfolding producer_discharged_identity
proof (intro allI impI)
  fix x y y'
  assume a: "(12,Pair_Term x y) \<in> positive_meaning artifact_identity_system"
    and b: "(12,Pair_Term x y') \<in> positive_meaning artifact_identity_system"
  from a obtain R where R: "artifact_value_presents R x" "artifact_value_presents R y"
    by (auto simp: artifact_identity_exact)
  from b obtain R' where R': "artifact_value_presents R' x" "artifact_value_presents R' y'"
    by (auto simp: artifact_identity_exact)
  have "R' = R" using R(1) R'(1) artifact_value_presents_unique by metis
  then show "artifact_citation_correspondence 12 0 y y'"
    using artifact_correspondence_at R(2) R'(2) by (simp add: artifact_citation_correspondence_def)
qed

lemma artifact_comparison_shape:
  assumes "(7,t) \<in> positive_meaning artifact_comparison_system"
  shows "\<exists>a e b f a' e' b' f'. t = Pair_Term (artifact_fields_term a e b f) (artifact_fields_term a' e' b' f')"
proof -
  have consequence: "(7,t) \<in> schema_consequences artifact_comparison_system (positive_meaning artifact_comparison_system)"
    using assms positive_meaning_unfold[of artifact_comparison_system] by blast
  obtain c S h where clause: "((7,c),S) \<in> system_clauses artifact_comparison_system"
    and head: "t = evaluate_pattern h (schema_conclusion S)"
    using schema_consequences_valuationD[OF consequence] by blast
  have "S = artifact_comparison_schema" using clause by simp
  then show ?thesis using head by (auto simp: artifact_comparison_schema_def)
qed

theorem comparison_producer_discharged:
  "producer_discharged (positive_meaning artifact_comparison_system) 7 view_identity [view_output]
    (artifact_citation_correspondence 7)"
  unfolding producer_discharged_identity
proof (intro allI impI)
  fix x y y'
  assume a: "(7,Pair_Term x y) \<in> positive_meaning artifact_comparison_system"
    and b: "(7,Pair_Term x y') \<in> positive_meaning artifact_comparison_system"
  obtain x0 x1 x2 x3 y0 y1 y2 y3 where
    s: "Pair_Term x y = Pair_Term (artifact_fields_term x0 x1 x2 x3) (artifact_fields_term y0 y1 y2 y3)"
    using artifact_comparison_shape[OF a] by blast
  obtain x0' x1' x2' x3' z0 z1 z2 z3 where
    s': "Pair_Term x y' = Pair_Term (artifact_fields_term x0' x1' x2' x3') (artifact_fields_term z0 z1 z2 z3)"
    using artifact_comparison_shape[OF b] by blast
  have x: "x = artifact_fields_term x0 x1 x2 x3" "y = artifact_fields_term y0 y1 y2 y3" using s by simp_all
  have x': "x0' = x0" "x1' = x1" "x2' = x2" "x3' = x3" "y' = artifact_fields_term z0 z1 z2 z3"
    using s' x(1) by simp_all
  have c: "(6,Pair_Term x0 y0) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x1 y1) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x2 y2) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x3 y3) \<in> positive_meaning bag_comparison_system"
    using a x by (simp_all add: artifact_comparison_fields)
  have d: "(6,Pair_Term x0 z0) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x1 z1) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x2 z2) \<in> positive_meaning bag_comparison_system"
    "(6,Pair_Term x3 z3) \<in> positive_meaning bag_comparison_system"
    using b x(1) x' by (simp_all add: artifact_comparison_fields)
  have g: "given_correspondence 6 y0 z0" "given_correspondence 6 y1 z1" "given_correspondence 6 y2 z2"
    "given_correspondence 6 y3 z3"
    using bag_answers_correspond c d by blast+
  show "artifact_citation_correspondence 7 0 y y'"
    unfolding artifact_citation_correspondence_def fields_correspondence_def
    using x(2) x'(5) g by auto
qed

text \<open>
  Two headed-material presentations of one artifact at one root present each collected field as one bag: the
  incidence rows and the functional values are distinct lists of one set, the counted values one count.
\<close>

lemma headed_material_correspond:
  assumes local: "headed_material_presents R k e b f" and local': "headed_material_presents R k e' b' f'"
    and fs: "term_formed e" "term_formed b" "term_formed f" "term_formed e'" "term_formed b'" "term_formed f'"
  shows "given_correspondence 6 e e'" "given_correspondence 6 b b'" "given_correspondence 6 f f'"
proof -
  obtain E B F where e: "e = data_list_term (map address_pair_data E)" and b: "b = data_list_term (map Payload_Term B)"
    and f: "f = data_list_term (map Payload_Term F)" and E: "distinct E" "set E = headed_incidence (object_structure R) k"
    and B: "count_list B = (\<lambda>v. bag_count (object_data R) (k,v))"
    and F: "distinct F" "set F = {v. (k,v) \<in> functional_bindings (object_data R)}"
    using local unfolding headed_material_presents_def by blast
  obtain E' B' F' where e': "e' = data_list_term (map address_pair_data E')"
    and b': "b' = data_list_term (map Payload_Term B')" and f': "f' = data_list_term (map Payload_Term F')"
    and E': "distinct E'" "set E' = headed_incidence (object_structure R) k"
    and B': "count_list B' = (\<lambda>v. bag_count (object_data R) (k,v))"
    and F': "distinct F'" "set F' = {v. (k,v) \<in> functional_bindings (object_data R)}"
    using local' unfolding headed_material_presents_def by blast
  have "mset E = mset E'" using E E' set_eq_iff_mset_eq_distinct by metis
  then have mE: "mset (map address_pair_data E) = mset (map address_pair_data E')" by simp
  have mB: "mset (map Payload_Term B) = mset (map Payload_Term B')"
  proof -
    have "mset B = mset B'" by (rule multiset_eqI) (simp add: count_mset B B')
    then show ?thesis by simp
  qed
  have "mset F = mset F'" using F F' set_eq_iff_mset_eq_distinct by metis
  then have mF: "mset (map Payload_Term F) = mset (map Payload_Term F')" by simp
  have el: "data_elements (map address_pair_data E)" "data_elements (map address_pair_data E')"
    "data_elements (map Payload_Term B)" "data_elements (map Payload_Term B')"
    "data_elements (map Payload_Term F)" "data_elements (map Payload_Term F')"
    using fs e e' b b' f f' by (auto simp: data_list_term_formed address_pair_data_def)
  show "given_correspondence 6 e e'" "given_correspondence 6 b b'" "given_correspondence 6 f f'"
    using bag_correspondence_lists[OF el(1,2) mE] bag_correspondence_lists[OF el(3,4) mB]
      bag_correspondence_lists[OF el(5,6) mF] e e' b b' f f' by simp_all
qed

theorem headed_producer_discharged:
  "producer_discharged (positive_meaning headed_material_system) 29 headed_fields_view headed_fields_holes
    (artifact_citation_correspondence 29)"
  unfolding producer_discharged_def headed_fields_view_holes
proof (intro allI impI)
  fix s t u v v' w w' i
  assume hs: "(29,s) \<in> positive_meaning headed_material_system"
    and ht: "(29,t) \<in> positive_meaning headed_material_system"
    and vs: "resolution_view_term headed_fields_view s = Some (u,v)"
    and vt: "resolution_view_term headed_fields_view t = Some (u,v')"
    and ws: "\<exists>a r e b f. s = headed_material_argument a r e b f \<and> w = [e,b,f]"
    and wt: "\<exists>a r e b f. t = headed_material_argument a r e b f \<and> w' = [e,b,f]"
    and i: "i < length headed_fields_holes"
  from ws obtain a r e b f where s: "s = headed_material_argument a r e b f" and w: "w = [e,b,f]" by blast
  from wt obtain a' r' e' b' f' where t: "t = headed_material_argument a' r' e' b' f'" and w': "w' = [e',b',f']"
    by blast
  have "u = Pair_Term a r" "u = Pair_Term a' r'"
    using vs vt s t by (auto simp: headed_fields_view_term)
  then have same: "a' = a" "r' = r" by simp_all
  obtain R k where R: "artifact_value_presents R a" and k: "r = Payload_Term k"
    and local: "headed_material_presents R k e b f"
    using hs s by (auto simp: headed_material_exact)
  obtain R' k' where R': "artifact_value_presents R' a" and k': "r = Payload_Term k'"
    and local': "headed_material_presents R' k' e' b' f'"
    using ht t same by (auto simp: headed_material_exact)
  have "R' = R" using R R' artifact_value_presents_unique by metis
  moreover have "k' = k" using k k' by simp
  ultimately have local': "headed_material_presents R k e' b' f'" using local' by simp
  have fs: "term_formed e" "term_formed b" "term_formed f" "term_formed e'" "term_formed b'" "term_formed f'"
    using positive_meaning_formed[OF hs] positive_meaning_formed[OF ht] s t
    by (simp_all add: headed_material_call)
  note c = headed_material_correspond[OF local local' fs]
  have "i = 0 \<or> i = 1 \<or> i = 2" using i by (auto simp: headed_fields_holes_def)
  then show "artifact_citation_correspondence 29 i (w ! i) (w' ! i)"
    using c w w' by (auto simp: artifact_citation_correspondence_def)
qed

theorem admission_producer_discharged:
  "producer_discharged (positive_meaning citation_admission_system) 36 inner_right_view
    [snd (snd inner_right_view)] (artifact_citation_correspondence 36)"
  unfolding producer_discharged_single inner_right_view_term
proof (intro allI impI)
  fix s t u v v'
  assume hs: "(36,s) \<in> positive_meaning citation_admission_system"
    and ht: "(36,t) \<in> positive_meaning citation_admission_system"
    and vs: "\<exists>a b c. s = Pair_Term (Pair_Term a b) (Pair_Term c v) \<and> u = Pair_Term (Pair_Term a b) c"
    and vt: "\<exists>a b c. t = Pair_Term (Pair_Term a b) (Pair_Term c v') \<and> u = Pair_Term (Pair_Term a b) c"
  from vs obtain p k c where s: "s = Pair_Term (Pair_Term p k) (Pair_Term c v)"
    and u: "u = Pair_Term (Pair_Term p k) c" by blast
  from vt obtain p' k' c' where t: "t = Pair_Term (Pair_Term p' k') (Pair_Term c' v')"
    and u': "u = Pair_Term (Pair_Term p' k') c'" by blast
  have same: "p' = p" "k' = k" "c' = c" using u u' by simp_all
  obtain R r d xs where R: "artifact_value_presents R p" and k: "k = Payload_Term r"
    and c: "c = citation_data_term d" and v: "v = data_list_term (map Payload_Term xs)"
    and xs: "distinct xs" "citation_at R r d (set xs)"
    using hs s by (auto simp: citation_admission_exact)
  obtain R' r' d' xs' where R': "artifact_value_presents R' p" and k': "k = Payload_Term r'"
    and c': "c = citation_data_term d'" and v': "v' = data_list_term (map Payload_Term xs')"
    and xs': "distinct xs'" "citation_at R' r' d' (set xs')"
    using ht t same by (auto simp: citation_admission_exact)
  have "R' = R" using R R' artifact_value_presents_unique by metis
  moreover have "r' = r" using k k' by simp
  moreover have "d' = d" using c c' citation_data_term_injective by (metis injD)
  ultimately have "set xs' = set xs" using xs(2) xs'(2) citation_at_unique by metis
  moreover have "term_formed v" "term_formed v'"
    using positive_meaning_formed[OF hs] positive_meaning_formed[OF ht] s t same
    by (simp_all add: citation_admission_call)
  ultimately show "artifact_citation_correspondence 36 0 v v'"
    using distinct_payload_bags[of xs xs'] xs(1) xs'(1) v v' by (simp add: artifact_citation_correspondence_def)
qed

theorem reading_producer_discharged:
  "producer_discharged (positive_meaning citation_reading_system) 42 outer_pair_view outer_pair_holes
    (artifact_citation_correspondence 42)"
  unfolding producer_discharged_def outer_pair_view_holes
proof (intro allI impI)
  fix s t u v v' w w' i
  assume hs: "(42,s) \<in> positive_meaning citation_reading_system"
    and ht: "(42,t) \<in> positive_meaning citation_reading_system"
    and vs: "resolution_view_term outer_pair_view s = Some (u,v)"
    and vt: "resolution_view_term outer_pair_view t = Some (u,v')"
    and ws: "\<exists>a b c v z. s = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term v z)) \<and> w = [v,z]"
    and wt: "\<exists>a b c v z. t = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term v z)) \<and> w' = [v,z]"
    and i: "i < length outer_pair_holes"
  from ws obtain e q k c z where s: "s = Pair_Term (Pair_Term e q) (Pair_Term k (Pair_Term c z))" and w: "w = [c,z]"
    by blast
  from wt obtain e' q' k' c' z' where t: "t = Pair_Term (Pair_Term e' q') (Pair_Term k' (Pair_Term c' z'))"
    and w': "w' = [c',z']" by blast
  have "u = Pair_Term (Pair_Term e q) k" "u = Pair_Term (Pair_Term e' q') k'"
    using vs vt s t by (auto simp: outer_pair_view_term)
  then have same: "e' = e" "q' = q" "k' = k" by simp_all
  obtain E x r d xs R where E: "environment_value_presents E e" and x: "q = use_data_term x" and r: "k = Payload_Term r"
    and d: "c = citation_data_term d" and z: "z = data_list_term (map Payload_Term xs)"
    and xs: "distinct xs" and at: "artifact_at E x R" and cite: "citation_at R r d (set xs)"
    using hs s by (auto simp: citation_reading_exact)
  obtain E' x' r' d' xs' R' where E': "environment_value_presents E' e" and x': "q = use_data_term x'"
    and r': "k = Payload_Term r'" and d': "c' = citation_data_term d'" and z': "z' = data_list_term (map Payload_Term xs')"
    and xs': "distinct xs'" and at': "artifact_at E' x' R'" and cite': "citation_at R' r' d' (set xs')"
    using ht t same by (auto simp: citation_reading_exact)
  have "E' = E" using E E' environment_value_presents_unique by metis
  moreover have "x' = x" using x x' use_data_term_injective by (metis injD)
  ultimately have "R' = R" using at at' environment_artifact_unique environment_value_presents_formed E by metis
  moreover have "r' = r" using r r' by simp
  ultimately have "d' = d \<and> set xs' = set xs" using cite cite' citation_at_unique by metis
  then have cc: "c' = c" and set: "set xs' = set xs" using d d' by simp_all
  have "term_formed z" "term_formed z'"
    using positive_meaning_formed[OF hs] positive_meaning_formed[OF ht] s t
    by (simp_all add: citation_reading_call)
  then have zz: "given_correspondence 6 z z'" using distinct_payload_bags[of xs xs'] xs xs' set z z' by simp
  have "i = 0 \<or> i = 1" using i by (auto simp: outer_pair_holes_def)
  then show "artifact_citation_correspondence 42 i (w ! i) (w' ! i)"
    using cc zz w w' by (auto simp: artifact_citation_correspondence_def)
qed

theorem resolution_producer_discharged:
  "producer_discharged (positive_meaning citation_resolution_system) 39 outer_pair_view
    [snd (snd outer_pair_view)] (artifact_citation_correspondence 39)"
  unfolding producer_discharged_single outer_pair_view_term
proof (intro allI impI)
  fix s t u v v'
  assume hs: "(39,s) \<in> positive_meaning citation_resolution_system"
    and ht: "(39,t) \<in> positive_meaning citation_resolution_system"
    and vs: "\<exists>a b c p q. s = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term p q)) \<and> u = Pair_Term (Pair_Term a b) c \<and>
      v = Pair_Term p q"
    and vt: "\<exists>a b c p q. t = Pair_Term (Pair_Term a b) (Pair_Term c (Pair_Term p q)) \<and> u = Pair_Term (Pair_Term a b) c \<and>
      v' = Pair_Term p q"
  from vs obtain e q c p y where s: "s = Pair_Term (Pair_Term e q) (Pair_Term c (Pair_Term p y))"
    and u: "u = Pair_Term (Pair_Term e q) c" and v: "v = Pair_Term p y" by blast
  from vt obtain e' q' c' p' y' where t: "t = Pair_Term (Pair_Term e' q') (Pair_Term c' (Pair_Term p' y'))"
    and u': "u = Pair_Term (Pair_Term e' q') c'" and v': "v' = Pair_Term p' y'" by blast
  have same: "e' = e" "q' = q" "c' = c" using u u' by simp_all
  obtain E x d g z where E: "environment_value_presents E e" and x: "q = use_data_term x"
    and d: "c = citation_data_term d" and g: "p = use_data_term g" and z: "target_value_presents z y"
    and route: "citation_route E x d g" and interp: "interpret_citation E x d z"
    using hs s unfolding citation_resolution_exact by (clarsimp; blast)
  obtain E' x' d' g' z' where E': "environment_value_presents E' e" and x': "q = use_data_term x'"
    and d': "c = citation_data_term d'" and g': "p' = use_data_term g'" and z': "target_value_presents z' y'"
    and route': "citation_route E' x' d' g'" and interp': "interpret_citation E' x' d' z'"
    using ht t same unfolding citation_resolution_exact by (clarsimp; blast)
  have EE: "E' = E" using E E' environment_value_presents_unique by metis
  have xx: "x' = x" using x x' use_data_term_injective by (metis injD)
  have dd: "d' = d" using d d' citation_data_term_injective by (metis injD)
  have formed: "environment_formed E" using E environment_value_presents_formed by metis
  have gg: "g' = g"
  proof (cases "citation_slots d = {}")
    case True then show ?thesis using route route' EE xx dd by simp
  next
    case False
    then obtain k where "k \<in> citation_slots d" by blast
    then have "binds_slot E x k g" "binds_slot E x k g'" using route route' EE xx dd by auto
    then show ?thesis using environment_binding_unique formed by metis
  qed
  have "z' = z" using interp interp' EE xx dd citation_interpretation_functional formed by metis
  then have "given_correspondence 45 y y'" using target_correspondence_at z z' by simp
  then show "artifact_citation_correspondence 39 0 v v'"
    using v v' g g' gg by (auto simp: artifact_citation_correspondence_def resolved_correspondence_def)
qed

theorem interpretation_producer_discharged:
  "producer_discharged (positive_meaning citation_interpretation_system) 40 inner_right_view
    [snd (snd inner_right_view)] (artifact_citation_correspondence 40)"
  unfolding producer_discharged_single inner_right_view_term
proof (intro allI impI)
  fix s t u v v'
  assume hs: "(40,s) \<in> positive_meaning citation_interpretation_system"
    and ht: "(40,t) \<in> positive_meaning citation_interpretation_system"
    and vs: "\<exists>a b c. s = Pair_Term (Pair_Term a b) (Pair_Term c v) \<and> u = Pair_Term (Pair_Term a b) c"
    and vt: "\<exists>a b c. t = Pair_Term (Pair_Term a b) (Pair_Term c v') \<and> u = Pair_Term (Pair_Term a b) c"
  from vs obtain e q c where s: "s = Pair_Term (Pair_Term e q) (Pair_Term c v)"
    and u: "u = Pair_Term (Pair_Term e q) c" by blast
  from vt obtain e' q' c' where t: "t = Pair_Term (Pair_Term e' q') (Pair_Term c' v')"
    and u': "u = Pair_Term (Pair_Term e' q') c'" by blast
  have same: "e' = e" "q' = q" "c' = c" using u u' by simp_all
  obtain E x d z where E: "environment_value_presents E e" and x: "q = use_data_term x"
    and d: "c = citation_data_term d" and z: "target_value_presents z v" and interp: "interpret_citation E x d z"
    using hs s by (auto simp: citation_interpretation_exact)
  obtain E' x' d' z' where E': "environment_value_presents E' e" and x': "q = use_data_term x'"
    and d': "c = citation_data_term d'" and z': "target_value_presents z' v'" and interp': "interpret_citation E' x' d' z'"
    using ht t same by (auto simp: citation_interpretation_exact)
  have "E' = E" using E E' environment_value_presents_unique by metis
  moreover have "x' = x" using x x' use_data_term_injective by (metis injD)
  moreover have "d' = d" using d d' citation_data_term_injective by (metis injD)
  moreover have "environment_formed E" using E environment_value_presents_formed by metis
  ultimately have "z' = z" using interp interp' citation_interpretation_functional by metis
  then show "artifact_citation_correspondence 40 0 v v'"
    using target_correspondence_at z z' by (simp add: artifact_citation_correspondence_def)
qed

theorem binder_producer_discharged:
  "producer_discharged (positive_meaning binder_admission_system) 54 view_identity [view_output]
    (artifact_citation_correspondence 54)"
  unfolding producer_discharged_identity
proof (intro allI impI)
  fix x y y'
  assume a: "(54,Pair_Term x y) \<in> positive_meaning binder_admission_system"
    and b: "(54,Pair_Term x y') \<in> positive_meaning binder_admission_system"
  obtain R p r Vs where x: "x = Pair_Term p (Payload_Term r)" and y: "y = data_list_term (map Payload_Term Vs)"
    and R: "artifact_value_presents R p" and d: "distinct Vs" and s: "binder_scope_at R r (set Vs)"
    using a by (auto simp: binder_admission_exact)
  obtain R' p' r' Vs' where x': "x = Pair_Term p' (Payload_Term r')" and y': "y' = data_list_term (map Payload_Term Vs')"
    and R': "artifact_value_presents R' p'" and d': "distinct Vs'" and s': "binder_scope_at R' r' (set Vs')"
    using b by (auto simp: binder_admission_exact)
  have same: "p' = p" "r' = r" using x x' by simp_all
  then have "R' = R" using R R' artifact_value_presents_unique by metis
  then have "set Vs = set Vs'" using s s' same binder_scope_unique by metis
  moreover have "term_formed y" "term_formed y'"
    using positive_meaning_formed[OF a] positive_meaning_formed[OF b] by (simp_all add: binder_admission_call)
  ultimately show "artifact_citation_correspondence 54 0 y y'"
    using distinct_payload_bags[of Vs Vs'] d d' y y' by (simp add: artifact_citation_correspondence_def)
qed

section \<open>The consumers the clauses derive\<close>

text \<open>
  A consumer holds a producer's output hole in a clause of the given's readers: 29, 32, 34, 35, 36 and 54 hold
  37's artifact; 11 holds 7's four fields; 21 and 31 hold 29's first field at 32's clause; 41 holds 42's citation;
  45 holds 40's target; 6, 48 and 55 hold 54's binders at their inputs and scope. Each is invariant under the
  producer's correspondence at the hole, by its notion's contract.
\<close>

lemma given_correspondence_sym:
  assumes "given_correspondence d y y'"
  shows "given_correspondence d y' y"
  using assms by (auto simp: given_correspondence_def presentation_transport_reverse[of _ _ y' y] split: if_splits)

lemma fields_correspondence_sym:
  assumes "fields_correspondence y y'"
  shows "fields_correspondence y' y"
  using assms given_correspondence_sym unfolding fields_correspondence_def by blast

lemma bag_lists:
  assumes "given_correspondence 6 y y'"
  obtains zs zs' where "y = data_list_term zs" "y' = data_list_term zs'" "mset zs = mset zs'"
    "data_elements zs" "data_elements zs'"
  using assms by (auto simp: given_correspondence_def presentation_transport_def data_bag_value_presents_def)

lemma mapped_bag_list:
  assumes inj: "inj f" and c: "given_correspondence 6 (data_list_term (map f A)) t"
  shows "\<exists>A'. t = data_list_term (map f A') \<and> mset A' = mset A"
proof -
  obtain xs ys where xs: "data_list_term (map f A) = data_list_term xs" and ys: "t = data_list_term ys"
    and m: "mset xs = mset ys"
    using c by (rule bag_lists) blast
  have xs': "xs = map f A" using xs by (simp add: data_list_term_injective)
  have "\<forall>y\<in>set ys. \<exists>a. y = f a" using mset_eq_setD[OF m] xs' by auto
  then have "\<exists>A'. ys = map f A'" by (simp add: ex_map_conv)
  then obtain A' where A': "ys = map f A'" by blast
  have "mset A' = mset A" using m xs' A' injective_mapped_multisets[OF inj] by metis
  then show ?thesis using ys A' by blast
qed

subsection \<open>The consumer views\<close>

text \<open>A rooted argument's artifact: 32's, 34's, 36's and 54's argument is a pair whose left pair begins with it.\<close>

definition rooted_artifact_view :: "nat resolution_view" where
  "rooted_artifact_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Variable 2),Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2),Finite_Variable 0)"

lemma rooted_artifact_view_formed: "view_formed rooted_artifact_view"
  by (auto simp: view_formed_def rooted_artifact_view_def fset_eq_iff)

lemma rooted_artifact_view_term:
  "resolution_view_term rooted_artifact_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>k m. t = Pair_Term (Pair_Term y k) m \<and> x = Pair_Term k m)"
  using resolution_view_term_values[OF rooted_artifact_view_formed[unfolded rooted_artifact_view_def], of 3 t x y]
  by (auto simp: rooted_artifact_view_def view_values_simps)

text \<open>The whole argument: 11's and 21's argument is the output they hold.\<close>

definition whole_view :: "nat resolution_view" where
  "whole_view = (Finite_Variable 0,Finite_Pattern_Payload [],Finite_Variable 0)"

lemma whole_view_formed: "view_formed whole_view"
  by (simp add: view_formed_def whole_view_def)

lemma whole_view_term: "resolution_view_term whole_view t = Some (x,y) \<longleftrightarrow> x = Payload_Term [] \<and> y = t"
  using resolution_view_term_values[OF whole_view_formed[unfolded whole_view_def], of "Suc 0" t x y]
  by (auto simp: whole_view_def view_values_simps)

text \<open>41's citation, the left of its argument's second pair.\<close>

definition citation_field_view :: "nat resolution_view" where
  "citation_field_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 3),
    Finite_Variable 2)"

lemma citation_field_view_formed: "view_formed citation_field_view"
  by (auto simp: view_formed_def citation_field_view_def fset_eq_iff)

lemma citation_field_view_term:
  "resolution_view_term citation_field_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>a b d. t = Pair_Term (Pair_Term a b) (Pair_Term y d) \<and> x = Pair_Term (Pair_Term a b) d)"
  using resolution_view_term_values[OF citation_field_view_formed[unfolded citation_field_view_def], of 4 t x y]
  by (auto simp: citation_field_view_def view_values_simps)

text \<open>48's second input, the middle of its three fields.\<close>

definition middle_view :: "nat resolution_view" where
  "middle_view = (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2),Finite_Variable 1)"

lemma middle_view_formed: "view_formed middle_view"
  by (auto simp: view_formed_def middle_view_def fset_eq_iff)

lemma middle_view_term:
  "resolution_view_term middle_view t = Some (x,y) \<longleftrightarrow> (\<exists>a z. t = Pair_Term a (Pair_Term y z) \<and> x = Pair_Term a z)"
  using resolution_view_term_values[OF middle_view_formed[unfolded middle_view_def], of 3 t x y]
  by (auto simp: middle_view_def view_values_simps)

text \<open>55's scope, the left of the pair beside the root in its argument.\<close>

definition scope_view :: "nat resolution_view" where
  "scope_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 3)
        (Finite_Variable 4)) (Finite_Variable 5))),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5))),
    Finite_Variable 3)"

lemma scope_view_formed: "view_formed scope_view"
  by (auto simp: view_formed_def scope_view_def fset_eq_iff)

lemma scope_view_term:
  "resolution_view_term scope_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>e u r b q. t = Pair_Term (Pair_Term e u) (Pair_Term r (Pair_Term (Pair_Term y b) q)) \<and>
      x = Pair_Term (Pair_Term e u) (Pair_Term r (Pair_Term b q)))"
  using resolution_view_term_values[OF scope_view_formed[unfolded scope_view_def], of 6 t x y]
  by (auto simp: scope_view_def view_values_simps)

subsection \<open>37's artifact held invariantly\<close>

lemma swap_artifact_consumer:
  assumes inv: "\<And>R a b x. artifact_value_presents R a \<Longrightarrow> artifact_value_presents R b \<Longrightarrow>
      (e,Pair_Term a x) \<in> M \<longleftrightarrow> (e,Pair_Term b x) \<in> M"
  shows "consumer_discharged M e view_swap (artifact_citation_correspondence 37 0)"
  unfolding consumer_view_simps(2)[symmetric] consumer_discharged_argument consumer_argument_def if_False
proof (intro allI impI)
  fix x y y' assume "artifact_citation_correspondence 37 0 y y'"
  then obtain R where "artifact_value_presents R y" "artifact_value_presents R y'"
    by (auto simp: artifact_citation_correspondence_def given_correspondence_def presentation_transport_def)
  then show "(e,Pair_Term y x) \<in> M \<longleftrightarrow> (e,Pair_Term y' x) \<in> M" by (rule inv)
qed

lemma rooted_artifact_consumer:
  assumes inv: "\<And>R a b k m. artifact_value_presents R a \<Longrightarrow> artifact_value_presents R b \<Longrightarrow>
      (e,Pair_Term (Pair_Term a k) m) \<in> M \<longleftrightarrow> (e,Pair_Term (Pair_Term b k) m) \<in> M"
  shows "consumer_discharged M e rooted_artifact_view (artifact_citation_correspondence 37 0)"
  unfolding consumer_discharged_def rooted_artifact_view_term
proof (intro allI impI)
  fix s t u v v'
  assume vs: "\<exists>k m. s = Pair_Term (Pair_Term v k) m \<and> u = Pair_Term k m"
    and vt: "\<exists>k m. t = Pair_Term (Pair_Term v' k) m \<and> u = Pair_Term k m"
    and c: "artifact_citation_correspondence 37 0 v v'"
  from vs vt obtain k m where s: "s = Pair_Term (Pair_Term v k) m" and t: "t = Pair_Term (Pair_Term v' k) m" by auto
  obtain R where R: "artifact_value_presents R v" "artifact_value_presents R v'"
    using c by (auto simp: artifact_citation_correspondence_def given_correspondence_def presentation_transport_def)
  show "(e,s) \<in> M \<longleftrightarrow> (e,t) \<in> M" using inv[OF R, of k m] s t by simp
qed

lemma headed_artifact_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R b"
  shows "(29,Pair_Term a x) \<in> positive_meaning headed_material_system \<longleftrightarrow>
    (29,Pair_Term b x) \<in> positive_meaning headed_material_system"
proof (cases "\<exists>k e c f. x = Pair_Term k (Pair_Term e (Pair_Term c f))")
  case True
  then obtain k e c f where x: "x = Pair_Term k (Pair_Term e (Pair_Term c f))" by blast
  show ?thesis using headed_material_presentation_invariance[OF assms, of k e c f] x by simp
next
  case False
  then show ?thesis by (auto simp: headed_material_exact)
qed

lemma admission_artifact_invariance:
  assumes "artifact_value_presents R a" "artifact_value_presents R b"
  shows "(36,Pair_Term (Pair_Term a k) m) \<in> positive_meaning citation_admission_system \<longleftrightarrow>
    (36,Pair_Term (Pair_Term b k) m) \<in> positive_meaning citation_admission_system"
proof (cases "\<exists>c i. m = Pair_Term c i")
  case True
  then obtain c i where m: "m = Pair_Term c i" by blast
  show ?thesis using citation_admission_presentation_invariance[OF assms, of k c i] m by simp
next
  case False
  then show ?thesis by (auto simp: citation_admission_exact)
qed

theorem headed_artifact_consumer:
  "consumer_discharged (positive_meaning headed_material_system) 29 view_swap (artifact_citation_correspondence 37 0)"
  by (rule swap_artifact_consumer) (rule headed_artifact_invariance)

theorem target_artifact_consumer:
  "consumer_discharged (positive_meaning target_admission_system) 35 view_swap (artifact_citation_correspondence 37 0)"
  by (rule swap_artifact_consumer) (rule target_admission_presentation_invariance)

theorem family_artifact_consumer:
  "consumer_discharged (positive_meaning family_admission_system) 32 rooted_artifact_view
    (artifact_citation_correspondence 37 0)"
  by (rule rooted_artifact_consumer) (rule family_admission_presentation_invariance)

theorem record_artifact_consumer:
  "consumer_discharged (positive_meaning record_admission_system) 34 rooted_artifact_view
    (artifact_citation_correspondence 37 0)"
  by (rule rooted_artifact_consumer) (rule record_admission_presentation_invariance)

theorem admission_artifact_consumer:
  "consumer_discharged (positive_meaning citation_admission_system) 36 rooted_artifact_view
    (artifact_citation_correspondence 37 0)"
  by (rule rooted_artifact_consumer) (rule admission_artifact_invariance)

theorem binder_artifact_consumer:
  "consumer_discharged (positive_meaning binder_admission_system) 54 rooted_artifact_view
    (artifact_citation_correspondence 37 0)"
  by (rule rooted_artifact_consumer) (rule binder_admission_presentation_invariance)

subsection \<open>7's fields held by artifact admission\<close>

lemma whole_consumer:
  assumes step: "\<And>v v'. corr v v' \<Longrightarrow> (e,v) \<in> M \<Longrightarrow> (e,v') \<in> M"
    and sym: "\<And>v v'. corr v v' \<Longrightarrow> corr v' v"
  shows "consumer_discharged M e whole_view corr"
  unfolding consumer_discharged_def whole_view_term using step sym by blast

lemma admission_fields_step:
  assumes R: "artifact_value_presents R y" and c: "fields_correspondence y y'"
  shows "artifact_value_presents R y'"
proof -
  obtain A E B F where e: "artifact_enumeration R A E B F" and y: "y = artifact_data_term A E B F"
    using R unfolding artifact_value_presents_def by blast
  obtain a0 e0 b0 f0 a1 e1 b1 f1 where y0: "y = artifact_fields_term a0 e0 b0 f0"
    and y1: "y' = artifact_fields_term a1 e1 b1 f1"
    and g: "given_correspondence 6 a0 a1" "given_correspondence 6 e0 e1" "given_correspondence 6 b0 b1"
      "given_correspondence 6 f0 f1"
    using c unfolding fields_correspondence_def by blast
  have fields: "a0 = data_list_term (map Payload_Term A)" "e0 = data_list_term (map incidence_data E)"
    "b0 = data_list_term (map address_pair_data B)" "f0 = data_list_term (map address_pair_data F)"
    using y y0 by (simp_all add: artifact_data_term_def)
  obtain A' where A': "a1 = data_list_term (map Payload_Term A')" "mset A' = mset A"
    using mapped_bag_list[OF payload_term_inj g(1)[unfolded fields(1)]] by blast
  obtain E' where E': "e1 = data_list_term (map incidence_data E')" "mset E' = mset E"
    using mapped_bag_list[OF incidence_data_injective g(2)[unfolded fields(2)]] by blast
  obtain B' where B': "b1 = data_list_term (map address_pair_data B')" "mset B' = mset B"
    using mapped_bag_list[OF address_pair_data_injective g(3)[unfolded fields(3)]] by blast
  obtain F' where F': "f1 = data_list_term (map address_pair_data F')" "mset F' = mset F"
    using mapped_bag_list[OF address_pair_data_injective g(4)[unfolded fields(4)]] by blast
  have d: "distinct A" "distinct E" "distinct F" using e by (simp_all add: artifact_enumeration_def)
  have d': "distinct A'" "distinct E'" "distinct F'"
    using d A'(2) E'(2) F'(2) by (metis mset_eq_imp_distinct_iff)+
  have s: "set A = set A'" "set E = set E'" "set F = set F'"
    using A'(2) E'(2) F'(2) by (metis mset_eq_setD)+
  have cnt: "count_list B = count_list B'"
    using B'(2) by (intro ext) (metis count_mset)
  have "artifact_enumeration R A' E' B' F'"
    using artifact_enumeration_order[OF d(1) d'(1) d(2) d'(2) d(3) d'(3) s(1,2) cnt s(3)] e by blast
  moreover have "y' = artifact_data_term A' E' B' F'"
    using y1 A'(1) E'(1) B'(1) F'(1) by (simp add: artifact_data_term_def)
  ultimately show ?thesis unfolding artifact_value_presents_def by blast
qed

theorem admission_fields_consumer:
  "consumer_discharged (positive_meaning artifact_admission_system) 11 whole_view (artifact_citation_correspondence 7 0)"
proof (rule whole_consumer)
  fix v v'
  assume c: "artifact_citation_correspondence 7 0 v v'" and h: "(11,v) \<in> positive_meaning artifact_admission_system"
  obtain R where R: "artifact_value_presents R v" using h by (auto simp: artifact_admission_exact)
  have "artifact_value_presents R v'"
    using admission_fields_step[OF R] c by (simp add: artifact_citation_correspondence_def)
  then show "(11,v') \<in> positive_meaning artifact_admission_system" by (auto simp: artifact_admission_exact)
next
  fix v v' assume "artifact_citation_correspondence 7 0 v v'"
  then show "artifact_citation_correspondence 7 0 v' v"
    using fields_correspondence_sym by (simp add: artifact_citation_correspondence_def)
qed

subsection \<open>29's incidence rows held at 32's clause\<close>

lemma keyed_rows_step:
  assumes c: "given_correspondence 6 v v'" and h: "(21,v) \<in> positive_meaning keyed_list_system"
  shows "(21,v') \<in> positive_meaning keyed_list_system"
proof -
  obtain xs where v: "v = pair_list_term xs" and f: "formed_key_rows xs" and d: "distinct (map fst xs)"
    using h by (auto simp: keyed_list_exact)
  have inj: "inj (\<lambda>(k,v). Pair_Term k v)" by (auto simp: inj_on_def)
  obtain xs' where v': "v' = pair_list_term xs'" and m: "mset xs' = mset xs"
    using mapped_bag_list[OF inj c[unfolded v]] by blast
  have "set xs' = set xs" using m by (metis mset_eq_setD)
  moreover have "distinct (map fst xs')" using d m by (metis mset_map mset_eq_imp_distinct_iff)
  ultimately show ?thesis unfolding keyed_list_exact using v' f by (intro exI[of _ xs']) auto
qed

theorem keyed_rows_consumer:
  "consumer_discharged (positive_meaning family_admission_system) 21 whole_view (artifact_citation_correspondence 29 0)"
proof (rule whole_consumer)
  fix v v'
  assume c: "artifact_citation_correspondence 29 0 v v'" and h: "(21,v) \<in> positive_meaning family_admission_system"
  show "(21,v') \<in> positive_meaning family_admission_system"
    using keyed_rows_step[of v v'] c h by (simp add: family_admission_components artifact_citation_correspondence_def)
next
  fix v v' assume "artifact_citation_correspondence 29 0 v v'"
  then show "artifact_citation_correspondence 29 0 v' v"
    using given_correspondence_sym by (simp add: artifact_citation_correspondence_def)
qed

theorem sockets_rows_consumer:
  "consumer_discharged (positive_meaning family_admission_system) 31 view_identity (artifact_citation_correspondence 29 0)"
  unfolding consumer_view_simps(1)[symmetric] consumer_discharged_argument consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "artifact_citation_correspondence 29 0 y y'"
  then have "given_correspondence 6 y y'" by (simp add: artifact_citation_correspondence_def)
  then obtain zs zs' where y: "y = data_list_term zs" and y': "y' = data_list_term zs'" and m: "mset zs = mset zs'"
    by (rule bag_lists)
  have "set zs = set zs'" using m by (rule mset_eq_setD)
  then show "(31,Pair_Term x y) \<in> positive_meaning family_admission_system \<longleftrightarrow>
      (31,Pair_Term x y') \<in> positive_meaning family_admission_system"
    using y y' by (simp add: family_admission_components family_socket_lists.lists)
qed

subsection \<open>42's citation and 40's target\<close>

theorem location_citation_consumer:
  "consumer_discharged (positive_meaning citation_location_system) 41 citation_field_view
    (artifact_citation_correspondence 42 0)"
  unfolding consumer_discharged_def citation_field_view_term by (auto simp: artifact_citation_correspondence_def)

theorem projection_target_consumer:
  "consumer_discharged (positive_meaning target_projection_system) 45 view_identity (artifact_citation_correspondence 40 0)"
  unfolding consumer_view_simps(1)[symmetric] consumer_discharged_argument consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "artifact_citation_correspondence 40 0 y y'"
  then obtain z where z: "target_value_presents z y" "target_value_presents z y'"
    by (auto simp: artifact_citation_correspondence_def given_correspondence_def presentation_transport_def)
  have "target_value_presents w y \<longleftrightarrow> target_value_presents w y'" for w
    using z target_value_presents_unique by metis
  then show "(45,Pair_Term x y) \<in> positive_meaning target_projection_system \<longleftrightarrow>
      (45,Pair_Term x y') \<in> positive_meaning target_projection_system"
    by (simp add: target_projection_exact)
qed

subsection \<open>54's binders at their inputs and scope\<close>

theorem bag_binders_consumer:
  "consumer_discharged (positive_meaning bag_comparison_system) 6 view_swap (artifact_citation_correspondence 54 0)"
  unfolding consumer_view_simps(2)[symmetric] consumer_discharged_argument consumer_argument_def if_False
proof (intro allI impI)
  fix x y y' assume "artifact_citation_correspondence 54 0 y y'"
  then have "given_correspondence 6 y y'" by (simp add: artifact_citation_correspondence_def)
  then obtain zs zs' where y: "y = data_list_term zs" and y': "y' = data_list_term zs'" and m: "mset zs = mset zs'"
    and e: "data_elements zs" "data_elements zs'"
    by (rule bag_lists)
  show "(6,Pair_Term y x) \<in> positive_meaning bag_comparison_system \<longleftrightarrow>
      (6,Pair_Term y' x) \<in> positive_meaning bag_comparison_system"
    using y y' m e by (auto simp: bag_comparison_exact data_list_term_injective)
qed

theorem union_left_consumer:
  "consumer_discharged (positive_meaning data_union_system) 48 view_swap (artifact_citation_correspondence 54 0)"
  unfolding consumer_view_simps(2)[symmetric] consumer_discharged_argument consumer_argument_def if_False
proof (intro allI impI)
  fix x y y' assume "artifact_citation_correspondence 54 0 y y'"
  then have "given_correspondence 6 y y'" by (simp add: artifact_citation_correspondence_def)
  then obtain zs zs' where y: "y = data_list_term zs" and y': "y' = data_list_term zs'" and m: "mset zs = mset zs'"
    and e: "data_elements zs" "data_elements zs'"
    by (rule bag_lists)
  show "(48,Pair_Term y x) \<in> positive_meaning data_union_system \<longleftrightarrow>
      (48,Pair_Term y' x) \<in> positive_meaning data_union_system"
    using y y' mset_eq_setD[OF m] e by (auto simp: data_union_exact data_list_term_injective)
qed

theorem union_middle_consumer:
  "consumer_discharged (positive_meaning data_union_system) 48 middle_view (artifact_citation_correspondence 54 0)"
  unfolding consumer_discharged_def middle_view_term
proof (intro allI impI)
  fix s t u v v'
  assume vs: "\<exists>a z. s = Pair_Term a (Pair_Term v z) \<and> u = Pair_Term a z"
    and vt: "\<exists>a z. t = Pair_Term a (Pair_Term v' z) \<and> u = Pair_Term a z"
    and c: "artifact_citation_correspondence 54 0 v v'"
  from vs vt obtain a z where s: "s = Pair_Term a (Pair_Term v z)" and t: "t = Pair_Term a (Pair_Term v' z)" by auto
  have "given_correspondence 6 v v'" using c by (simp add: artifact_citation_correspondence_def)
  then obtain zs zs' where y: "v = data_list_term zs" and y': "v' = data_list_term zs'" and m: "mset zs = mset zs'"
    and e: "data_elements zs" "data_elements zs'"
    by (rule bag_lists)
  show "(48,s) \<in> positive_meaning data_union_system \<longleftrightarrow> (48,t) \<in> positive_meaning data_union_system"
    using s t y y' mset_eq_setD[OF m] e by (auto simp: data_union_exact data_list_term_injective)
qed

lemma instantiation_scope_step:
  assumes c: "given_correspondence 6 v v'"
    and h: "(55,Pair_Term (Pair_Term e u) (Pair_Term r (Pair_Term (Pair_Term v b) q)))
      \<in> positive_meaning pattern_instantiation_system"
  shows "(55,Pair_Term (Pair_Term e u) (Pair_Term r (Pair_Term (Pair_Term v' b) q)))
      \<in> positive_meaning pattern_instantiation_system"
proof -
  obtain E u0 Vs xs r0 t0 Us Is Ks where u: "u = use_data_term u0" and v: "v = data_list_term (map Payload_Term Vs)"
    and b: "b = binding_rows_term xs" and r: "r = Payload_Term r0"
    and q: "q = Pair_Term t0 (Pair_Term (data_list_term (map Payload_Term Us))
      (Pair_Term (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks))))"
    and source: "environment_value_presents E e"
    using h unfolding pattern_instantiation_exact by auto
  obtain Ws where v': "v' = data_list_term (map Payload_Term Ws)" and m: "mset Ws = mset Vs"
    using mapped_bag_list[OF payload_term_inj c[unfolded v]] by blast
  show ?thesis
    using h pattern_instantiation_orders[OF source m[symmetric] refl refl refl refl] u v v' b r q by simp
qed

theorem instantiation_scope_consumer:
  "consumer_discharged (positive_meaning pattern_instantiation_system) 55 scope_view (artifact_citation_correspondence 54 0)"
  unfolding consumer_discharged_def scope_view_term
proof (intro allI impI)
  fix s t u v v'
  assume vs: "\<exists>e w r b q. s = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term (Pair_Term v b) q)) \<and>
      u = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term b q))"
    and vt: "\<exists>e w r b q. t = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term (Pair_Term v' b) q)) \<and>
      u = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term b q))"
    and c: "artifact_citation_correspondence 54 0 v v'"
  from vs vt obtain e w r b q where s: "s = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term (Pair_Term v b) q))"
    and t: "t = Pair_Term (Pair_Term e w) (Pair_Term r (Pair_Term (Pair_Term v' b) q))" by auto
  have c': "given_correspondence 6 v v'" using c by (simp add: artifact_citation_correspondence_def)
  show "(55,s) \<in> positive_meaning pattern_instantiation_system \<longleftrightarrow> (55,t) \<in> positive_meaning pattern_instantiation_system"
    using instantiation_scope_step[OF c'] instantiation_scope_step[OF given_correspondence_sym[OF c']] s t by blast
qed

section \<open>The sockets, discharged along the clauses' carriers\<close>

text \<open>
  A free socket inside a declared producer's clause is discharged by the carrying lemma
  (@{thm [source] socket_discharged_carried}): the socket's producer is discharged at the clause's system with its
  class, the consumers holding its output in the same clause are its carriers, and the head holds the carried
  variables only inside its output at the parent's view. Each clause is the finite schema that decodes to the
  program's own.
\<close>

lemma artifact_citation_correspondence_simps:
  "artifact_citation_correspondence 37 = (\<lambda>_. given_correspondence 10)"
  "artifact_citation_correspondence 12 = (\<lambda>_. given_correspondence 10)"
  "artifact_citation_correspondence 7 = (\<lambda>_. fields_correspondence)"
  "artifact_citation_correspondence 29 = (\<lambda>_. given_correspondence 6)"
  "artifact_citation_correspondence 36 = (\<lambda>_. given_correspondence 6)"
  "artifact_citation_correspondence 54 = (\<lambda>_. given_correspondence 6)"
  "artifact_citation_correspondence 39 = (\<lambda>_. resolved_correspondence)"
  "artifact_citation_correspondence 40 = (\<lambda>_. given_correspondence 45)"
  by (simp_all add: artifact_citation_correspondence_def fun_eq_iff)

lemma given_correspondence_symp: "symp (given_correspondence d)"
  using given_correspondence_sym by (blast intro: sympI)

lemma fields_correspondence_symp: "symp fields_correspondence"
  using fields_correspondence_sym by (blast intro: sympI)

subsection \<open>The views the listed sockets read\<close>

text \<open>
  Every socket below is carried by @{text socket_carried_listed}: the views read through their parts, a consumer's
  input read through @{const consumer_input} at the identity and whole views.
\<close>

lemmas artifact_citation_listed_simps = socket_listed_simps view_listed[OF lookup_view_def]
  view_listed[OF inner_right_view_def] view_listed[OF outer_pair_view_def] view_listed[OF headed_fields_view_def]
  view_listed[OF whole_view_def] lookup_view_formed outer_pair_view_formed headed_fields_view_formed whole_view_formed
  consumer_input_def whole_view_term view_identity_term pair_view_some

subsection \<open>12 inside 37: the stored artifact compared with the output\<close>

definition lookup_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "lookup_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,26,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)),
      (1,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4))
        (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 5))),
      (2,12,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 3))|},
    finite_schema_materials = {||}\<rparr>"

lemma lookup_socket_decoded: "decode_finite_schema lookup_socket_schema = artifact_lookup_schema"
  by (simp add: lookup_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def artifact_lookup_schema_def)

lemma lookup_identity_producer:
  "producer_discharged (positive_meaning artifact_lookup_system) 12 view_identity [snd (snd view_identity)]
    (\<lambda>_. given_correspondence 10)"
proof -
  have eq: "\<And>t. (12,t) \<in> positive_meaning artifact_lookup_system \<longleftrightarrow> (12,t) \<in> positive_meaning artifact_identity_system"
    by (simp add: artifact_lookup_components artifact_identity_exact)
  show ?thesis unfolding producer_discharged_site[OF eq] view_identity_output
    using identity_producer_discharged by (simp add: artifact_citation_correspondence_simps)
qed

theorem lookup_socket_discharged:
  "socket_discharged (positive_meaning artifact_lookup_system) lookup_socket_schema 2 False view_identity lookup_view"
  by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed lookup_identity_producer, where \<sigma> = "\<lambda>_. 1" and cs = "[]"]])
    (simp add: artifact_citation_listed_simps lookup_socket_schema_def)

subsection \<open>7 inside 12: the two admitted artifacts compared, 11 carrying the output\<close>

definition identity_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "identity_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises = {|(0,11,Finite_Variable 0),(1,11,Finite_Variable 1),
      (2,7,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))|},
    finite_schema_materials = {||}\<rparr>"

lemma identity_socket_decoded: "decode_finite_schema identity_socket_schema = artifact_identity_schema"
  by (simp add: identity_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def artifact_identity_schema_def)

lemma identity_comparison_producer:
  "producer_discharged (positive_meaning artifact_identity_system) 7 view_identity [snd (snd view_identity)]
    (\<lambda>_. fields_correspondence)"
proof -
  have eq: "\<And>t. (7,t) \<in> positive_meaning artifact_identity_system \<longleftrightarrow> (7,t) \<in> positive_meaning artifact_comparison_system"
    by (rule artifact_identity_old_meaning) simp
  show ?thesis unfolding producer_discharged_site[OF eq] view_identity_output
    using comparison_producer_discharged by (simp add: artifact_citation_correspondence_simps)
qed

lemma identity_admission_consumer:
  "consumer_discharged (positive_meaning artifact_identity_system) 11 whole_view fields_correspondence"
proof -
  have eq: "\<And>t. (11,t) \<in> positive_meaning artifact_identity_system \<longleftrightarrow> (11,t) \<in> positive_meaning artifact_admission_system"
    by (rule artifact_identity_previous_meaning) simp
  show ?thesis unfolding consumer_discharged_site[OF eq]
    using admission_fields_consumer by (simp add: artifact_citation_correspondence_simps)
qed

abbreviation identity_carriers :: "nat clause_carrier list" where
  "identity_carriers \<equiv> [(1,consumer_carrier_view whole_view,consumer_input whole_view fields_correspondence,(=))]"

theorem identity_socket_discharged:
  "socket_discharged (positive_meaning artifact_identity_system) identity_socket_schema 2 False view_identity view_identity"
  by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed identity_comparison_producer, where \<sigma> = "\<lambda>_. 1" and cs = "identity_carriers"]])
    (simp add: artifact_citation_listed_simps identity_socket_schema_def
      consumer_discharged_carrier[OF whole_view_formed fields_correspondence_symp, THEN iffD1, OF identity_admission_consumer])

subsection \<open>6 inside 7: each field's bag comparison\<close>

definition comparison_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "comparison_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))))
      (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 5)
        (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 7)))),
    finite_schema_premises = {|(0,6,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 4)),
      (1,6,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 5)),
      (2,6,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 6)),
      (3,6,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 7))|},
    finite_schema_materials = {||}\<rparr>"

lemma comparison_socket_decoded: "decode_finite_schema comparison_socket_schema = artifact_comparison_schema"
  by (simp add: comparison_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def artifact_comparison_schema_def)

lemma comparison_bag_producer:
  "producer_discharged (positive_meaning artifact_comparison_system) 6 view_identity [snd (snd view_identity)]
    (\<lambda>_. given_correspondence 6)"
proof -
  have eq: "\<And>t. (6,t) \<in> positive_meaning artifact_comparison_system \<longleftrightarrow> (6,t) \<in> positive_meaning bag_comparison_system"
    by (rule artifact_comparison_old_meaning) simp
  show ?thesis unfolding producer_discharged_site[OF eq] view_identity_output by (rule bag_producer_discharged)
qed

theorem comparison_socket_discharged:
  assumes i: "i \<in> {0,1,2,3}"
  shows "socket_discharged (positive_meaning artifact_comparison_system) comparison_socket_schema i False
    view_identity view_identity"
proof -
  have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" using i by simp
  then show ?thesis
    apply (elim disjE)
    apply (simp only:, rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed comparison_bag_producer, where \<sigma> = "\<lambda>_. 1" and cs = "[]"]], simp add: artifact_citation_listed_simps comparison_socket_schema_def)+
    done
qed

subsection \<open>6 inside 29: each collected field's bag comparison\<close>

definition headed_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "headed_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))))
      (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 5)
        (Finite_Pattern_Pair (Finite_Variable 6) (Finite_Variable 7)))),
    finite_schema_premises = {|(0,11,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))),
      (1,5,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 11))),
      (2,28,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 8))),
      (3,28,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 9))),
      (4,28,Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 10))),
      (5,6,Finite_Pattern_Pair (Finite_Variable 8) (Finite_Variable 5)),
      (6,6,Finite_Pattern_Pair (Finite_Variable 9) (Finite_Variable 6)),
      (7,6,Finite_Pattern_Pair (Finite_Variable 10) (Finite_Variable 7))|},
    finite_schema_materials = {||}\<rparr>"

lemma headed_socket_decoded: "decode_finite_schema headed_socket_schema = headed_material_schema"
  by (simp add: headed_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def headed_material_schema_def)

lemma headed_bag_producer:
  "producer_discharged (positive_meaning headed_material_system) 6 view_identity [snd (snd view_identity)]
    (\<lambda>_. given_correspondence 6)"
  unfolding producer_discharged_site[OF headed_material_components(3)] view_identity_output
  by (rule bag_producer_discharged)

theorem headed_socket_discharged:
  assumes i: "i \<in> {5,6,7}"
  shows "socket_discharged (positive_meaning headed_material_system) headed_socket_schema i False
    view_identity headed_fields_view"
proof -
  have "i = 5 \<or> i = 6 \<or> i = 7" using i by simp
  then show ?thesis
    apply (elim disjE)
    apply (simp only:, rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed headed_bag_producer, where \<sigma> = "\<lambda>_. 1" and cs = "[]"]], simp add: artifact_citation_listed_simps headed_socket_schema_def)+
    done
qed

subsection \<open>29 inside 32: a root's incidence rows, carried by 21 and 31\<close>

text \<open>
  At 32's clause the root's counted and functional fields are fixed empty: the socket's view reads 29's argument
  with those fields in its input and the incidence rows its output.
\<close>

definition headed_incidence_view :: "nat resolution_view" where
  "headed_incidence_view = (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)))),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
      (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))),Finite_Variable 2)"

lemma headed_incidence_view_formed: "view_formed headed_incidence_view"
  by (auto simp: view_formed_def headed_incidence_view_def fset_eq_iff)

lemma headed_incidence_view_term:
  "resolution_view_term headed_incidence_view t = Some (x,y) \<longleftrightarrow>
    (\<exists>a r b f. t = headed_material_argument a r y b f \<and> x = Pair_Term a (Pair_Term r (Pair_Term b f)))"
  using resolution_view_term_values[OF headed_incidence_view_formed[unfolded headed_incidence_view_def], of 5 t x y]
  by (auto simp: headed_incidence_view_def view_values_simps)

lemma headed_incidence_producer:
  "producer_discharged (positive_meaning headed_material_system) 29 headed_incidence_view
    [snd (snd headed_incidence_view)] (\<lambda>_. given_correspondence 6)"
  unfolding producer_discharged_single headed_incidence_view_term
proof (intro allI impI)
  fix s t u v v'
  assume hs: "(29,s) \<in> positive_meaning headed_material_system"
    and ht: "(29,t) \<in> positive_meaning headed_material_system"
    and vs: "\<exists>a r b f. s = headed_material_argument a r v b f \<and> u = Pair_Term a (Pair_Term r (Pair_Term b f))"
    and vt: "\<exists>a r b f. t = headed_material_argument a r v' b f \<and> u = Pair_Term a (Pair_Term r (Pair_Term b f))"
  from vs vt obtain a r b f where s: "s = headed_material_argument a r v b f"
    and t: "t = headed_material_argument a r v' b f" by auto
  obtain R k where R: "artifact_value_presents R a" and k: "r = Payload_Term k"
    and local: "headed_material_presents R k v b f"
    using hs s by (auto simp: headed_material_exact)
  obtain R' k' where R': "artifact_value_presents R' a" and k': "r = Payload_Term k'"
    and local': "headed_material_presents R' k' v' b f"
    using ht t by (auto simp: headed_material_exact)
  have "R' = R" using R R' artifact_value_presents_unique by metis
  moreover have "k' = k" using k k' by simp
  ultimately have local': "headed_material_presents R k v' b f" using local' by simp
  have fs: "term_formed v" "term_formed b" "term_formed f" "term_formed v'" "term_formed b" "term_formed f"
    using meaning_answers_formed[of headed_material_system, rule_format, OF hs]
      meaning_answers_formed[of headed_material_system, rule_format, OF ht] s t by simp_all
  show "given_correspondence 6 v v'" by (rule headed_material_correspond(1)[OF local local' fs])
qed

definition family_rows_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "family_rows_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,29,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))))),
      (1,21,Finite_Variable 2),
      (2,31,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2))|},
    finite_schema_materials = {||}\<rparr>"

lemma family_rows_socket_decoded: "decode_finite_schema family_rows_socket_schema = family_admission_schema"
  by (simp add: family_rows_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def family_admission_schema_def)

abbreviation family_carriers :: "nat clause_carrier list" where
  "family_carriers \<equiv> [(1,consumer_carrier_view whole_view,consumer_input whole_view (given_correspondence 6),(=)),
    (2,consumer_carrier_view view_identity,consumer_input view_identity (given_correspondence 6),(=))]"

theorem family_rows_socket_discharged:
  "socket_discharged (positive_meaning family_admission_system) family_rows_socket_schema 0 False
    headed_incidence_view view_identity"
proof -
  let ?M = "positive_meaning family_admission_system"
  have producer: "producer_discharged ?M 29 headed_incidence_view [snd (snd headed_incidence_view)]
      (\<lambda>_. given_correspondence 6)"
    unfolding producer_discharged_site[OF family_admission_components(1)] by (rule headed_incidence_producer)
  have c21: "consumer_discharged ?M 21 whole_view (given_correspondence 6)"
    using keyed_rows_consumer by (simp add: artifact_citation_correspondence_simps)
  have c31: "consumer_discharged ?M 31 view_identity (given_correspondence 6)"
    using sockets_rows_consumer by (simp add: artifact_citation_correspondence_simps)
  show ?thesis
    by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed headed_incidence_view_formed
      producer, where \<sigma> = "\<lambda>_. 2" and cs = family_carriers]])
      (simp add: artifact_citation_listed_simps family_rows_socket_schema_def view_listed[OF headed_incidence_view_def]
        consumer_discharged_carrier[OF whole_view_formed given_correspondence_symp, THEN iffD1, OF c21]
        consumer_discharged_carrier[OF view_identity_formed given_correspondence_symp, THEN iffD1, OF c31])
qed

subsection \<open>39 inside 40: the resolved use and target\<close>

definition interpretation_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "interpretation_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,39,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 3))))|},
    finite_schema_materials = {||}\<rparr>"

lemma interpretation_socket_decoded: "decode_finite_schema interpretation_socket_schema = citation_interpretation_schema"
  by (simp add: interpretation_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def citation_interpretation_schema_def)

lemma interpretation_resolution_producer:
  "producer_discharged (positive_meaning citation_interpretation_system) 39 outer_pair_view
    [snd (snd outer_pair_view)] (\<lambda>_. resolved_correspondence)"
  unfolding producer_discharged_site[OF citation_interpretation_resolution]
  using resolution_producer_discharged by (simp add: artifact_citation_correspondence_simps)

theorem interpretation_socket_discharged:
  "socket_discharged (positive_meaning citation_interpretation_system) interpretation_socket_schema 0 False
    outer_pair_view inner_right_view"
  by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed outer_pair_view_formed interpretation_resolution_producer, where \<sigma> = "\<lambda>v. if v = 4 then 3 else 4" and cs = "[]"]])
    (simp add: artifact_citation_listed_simps interpretation_socket_schema_def)

subsection \<open>6 inside 36's external clause: the interior's bag of the slot and the target\<close>

definition external_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "external_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Pattern_Payload []))
        (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Payload []))) (Finite_Variable 5)),
    finite_schema_premises = {|(0,29,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))
          (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)) (Finite_Pattern_Payload [])))
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []))))),
      (1,29,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 3)
        (Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Pair (Finite_Pattern_Payload [])
          (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Pattern_Payload [])))))),
      (2,3,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
      (3,3,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)),
      (4,3,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
      (5,6,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1)
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Payload []))) (Finite_Variable 5))|},
    finite_schema_materials = {||}\<rparr>"

lemma external_socket_decoded: "decode_finite_schema external_socket_schema = citation_external_schema"
  by (simp add: external_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def citation_external_schema_def)

lemma admission_bag_producer:
  "producer_discharged (positive_meaning citation_admission_system) 6 view_identity [snd (snd view_identity)]
    (\<lambda>_. given_correspondence 6)"
  unfolding producer_discharged_site[OF citation_admission_components(3)] view_identity_output
  by (rule bag_producer_discharged)

theorem external_socket_discharged:
  "socket_discharged (positive_meaning citation_admission_system) external_socket_schema 5 False
    view_identity inner_right_view"
  by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed admission_bag_producer, where \<sigma> = "\<lambda>_. 1" and cs = "[]"]])
    (simp add: artifact_citation_listed_simps external_socket_schema_def)

subsection \<open>32 inside 54: the binder family's rows, carried by 53 to the binders\<close>

text \<open>
  At 54's clause 32's rows reach the head's binders through 53, the diagonal rows of a binder list read against its
  direction. 53 is a function witness from a bag of formed terms to the bag of their diagonal rows
  (@{thm [source] diagonal_rows_exact}), read along the rows: every presentation of a bag's diagonal rows is the
  diagonal of some presentation of the bag. 32's two answers at one input are formed and present one set of
  distinct rows, so they present one bag of rows (the class the carrier reads).
\<close>

lemma list_all2_formed_terms:
  "list_all2 (\<lambda>x p. term_formed x \<and> p = x) xs ps \<longleftrightarrow> ps = xs \<and> (\<forall>x\<in>set xs. term_formed x)"
  by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)

abbreviation formed_bag_presents :: "factor_term multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "formed_bag_presents \<equiv> data_bag_presents formed_term_presents"

lemma formed_bag_presents_terms:
  "formed_bag_presents N t \<longleftrightarrow>
    (\<exists>ys. mset ys = N \<and> (\<forall>y\<in>set ys. term_formed y) \<and> t = data_list_term ys)"
  by (auto simp: data_bag_presents_def data_sequence_presents_def list_all2_formed_terms)

theorem diagonal_rows_witness:
  "presented_function_witness (formed_bag_presents) (\<lambda>M. \<forall>a\<in>set_mset M. term_formed a)
    (\<lambda>t. \<exists>ps. (\<forall>p\<in>set ps. term_formed p) \<and> t = data_list_term ps) row_bag_presents rows_formed
    (\<lambda>t. \<exists>N. row_bag_presents N t) (image_mset (\<lambda>x. (x,x)))
    (\<lambda>p q. (53,Pair_Term p q) \<in> positive_meaning binder_admission_system)"
proof (rule presented_function_witness.intro[OF data_bag_presentation_class[OF formed_term_presentation_class]
    row_bag_presentation_class]; unfold_locales)
  fix p q assume "(53,Pair_Term p q) \<in> positive_meaning binder_admission_system"
  then show "\<exists>ps. (\<forall>p\<in>set ps. term_formed p) \<and> p = data_list_term ps"
    by (auto simp: binder_admission_components diagonal_rows_exact data_list_term_formed)
next
  fix a p q assume R: "formed_bag_presents a p"
    and h: "(53,Pair_Term p q) \<in> positive_meaning binder_admission_system"
  obtain ys where ys: "mset ys = a" "p = data_list_term ys" using R by (auto simp: formed_bag_presents_terms)
  obtain xs where xs: "p = data_list_term xs" "q = pair_list_term (map (\<lambda>x. (x,x)) xs)"
    "term_formed (data_list_term xs)"
    using h by (auto simp: binder_admission_components diagonal_rows_exact)
  have "xs = ys" using xs(1) ys(2) by (simp add: data_list_term_injective)
  then show "row_bag_presents (image_mset (\<lambda>x. (x,x)) a) q"
    using xs ys unfolding row_bag_presents_rows
    by (intro exI[of _ "map (\<lambda>x. (x,x)) xs"]) (auto simp: pair_list_term_formed_iff data_list_term_formed)
next
  fix p assume "\<exists>ps. (\<forall>p\<in>set ps. term_formed p) \<and> p = data_list_term ps"
  then obtain ps where ps: "\<forall>p\<in>set ps. term_formed p" "p = data_list_term ps" by blast
  show "\<exists>q. (53,Pair_Term p q) \<in> positive_meaning binder_admission_system"
    unfolding binder_admission_components diagonal_rows_exact
    using ps by (auto simp: data_list_term_formed)
qed

lemma diagonal_rows_along:
  assumes R: "formed_bag_presents a q"
    and S: "row_bag_presents (image_mset (\<lambda>x. (x,x)) a) p'"
  shows "\<exists>q'. formed_bag_presents a q' \<and>
    (53,Pair_Term q' p') \<in> positive_meaning binder_admission_system"
proof -
  obtain zs where zs: "mset zs = image_mset (\<lambda>x. (x,x)) a" "term_formed (pair_list_term zs)" "p' = pair_list_term zs"
    using S by (auto simp: row_bag_presents_rows)
  have "set zs = (\<lambda>x. (x,x)) ` set_mset a" using arg_cong[OF zs(1), of set_mset] by simp
  then have diag: "\<forall>z\<in>set zs. snd z = fst z" by auto
  have m: "mset (map fst zs) = a" using zs(1) by (simp add: multiset.map_comp comp_def)
  have rediagonal: "map (\<lambda>x. (x,x)) (map fst zs) = zs" using diag by (induction zs) auto
  have f: "\<forall>y\<in>set (map fst zs). term_formed y" using zs(2) by (auto simp: pair_list_term_formed_iff)
  have holds: "(53,Pair_Term (data_list_term (map fst zs)) p') \<in> positive_meaning binder_admission_system"
    unfolding binder_admission_components diagonal_rows_exact
    by (intro exI[of _ "map fst zs"]) (use rediagonal zs(3) f in \<open>simp add: data_list_term_formed\<close>)
  have r: "formed_bag_presents a (data_list_term (map fst zs))"
    unfolding formed_bag_presents_terms using m f by blast
  show ?thesis using holds r by blast
qed

abbreviation binder_bag_transport :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "binder_bag_transport \<equiv> presentation_transport formed_bag_presents formed_bag_presents"

theorem diagonal_rows_carrier:
  "carrier_discharged (positive_meaning binder_admission_system) 53 view_swap row_bag_transport binder_bag_transport"
  by (rule witness_along_carrier[OF diagonal_rows_witness diagonal_rows_along]) (auto simp: view_swap_term swap_view_some)

lemma family_rows_bag:
  assumes c: "given_correspondence 32 y y'" and f: "term_formed y" "term_formed y'"
  shows "row_bag_transport y y'"
proof -
  obtain rs rs' where d: "distinct rs" "distinct rs'" and m: "mset rs = mset rs'"
      and rs: "y = data_list_term (map address_pair_data rs)" and rs': "y' = data_list_term (map address_pair_data rs')"
    by (rule family_rows_enumerations[OF c])
  let ?row = "\<lambda>z::local_address \<times> octets. (Payload_Term (fst z),Payload_Term (snd z))"
  have rows: "data_list_term (map address_pair_data zs) = pair_list_term (map ?row zs)" for zs
    by (induction zs) (simp_all add: address_pair_data_def)
  have "row_bag_presents (mset (map ?row rs)) y" "row_bag_presents (mset (map ?row rs)) y'"
    using rs rs' f m unfolding row_bag_presents_rows rows by (metis mset_map)+
  then show ?thesis by (auto simp: presentation_transport_def)
qed

lemma binder_family_producer:
  "producer_discharged (positive_meaning binder_admission_system) 32 view_identity [snd (snd view_identity)]
    (\<lambda>_. row_bag_transport)"
proof -
  have step: "row_bag_transport y y'"
    if a0: "(32,Pair_Term x y) \<in> positive_meaning binder_admission_system"
      and b0: "(32,Pair_Term x y') \<in> positive_meaning binder_admission_system" for x y y'
  proof -
    have a: "(32,Pair_Term x y) \<in> positive_meaning family_admission_system"
      and b: "(32,Pair_Term x y') \<in> positive_meaning family_admission_system"
      using a0 b0 binder_admission_components(2) by blast+
    have c: "given_correspondence 32 y y'"
      using family_producer_discharged a b unfolding producer_discharged_identity by blast
    have "term_formed (Pair_Term x y)" "term_formed (Pair_Term x y')"
      using meaning_answers_formed[of family_admission_system, rule_format, OF a]
        meaning_answers_formed[of family_admission_system, rule_format, OF b] by simp_all
    then show ?thesis using family_rows_bag[OF c] by simp
  qed
  show ?thesis
    unfolding view_identity_output producer_discharged_identity using step by blast
qed

definition binder_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "binder_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,53,Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
      (1,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 3))|},
    finite_schema_materials = {||}\<rparr>"

lemma binder_socket_decoded: "decode_finite_schema binder_socket_schema = binder_admission_schema"
  by (simp add: binder_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def binder_admission_schema_def)

abbreviation binder_carriers :: "nat clause_carrier list" where
  "binder_carriers \<equiv> [(0,view_swap,row_bag_transport,binder_bag_transport)]"

theorem binder_socket_discharged:
  "socket_discharged (positive_meaning binder_admission_system) binder_socket_schema 1 False view_identity view_identity"
  by (rule socket_discharged_carried[OF socket_carried_listed[OF meaning_answers_formed view_identity_formed binder_family_producer, where \<sigma> = "\<lambda>_. 1" and cs = "binder_carriers"]])
    (simp add: artifact_citation_listed_simps binder_socket_schema_def diagonal_rows_carrier)

section \<open>The declarations, each at its notion's system\<close>

text \<open>
  Each notion's declarations: its producer at its view with its sockets, and the consumers standing at it, each
  discharged at the notion's own system with the one correspondence @{const artifact_citation_correspondence},
  indexed by the producer's site and hole. The parent of every socket is committed at the socket's head view: 37,
  12, 7, 29, 36, 42 and 40 here, 32 at R6's identity view.
\<close>

definition lookup_declarations :: "(nat,nat,nat) resolution_declarations" where
  "lookup_declarations = \<lparr>declared_producers = {|(37,lookup_view,[snd (snd lookup_view)])|}, declared_consumers = {||},
    declared_sockets = {|(37,lookup_socket_schema,2,False,view_identity,lookup_view)|}\<rparr>"

definition identity_declarations :: "(nat,nat,nat) resolution_declarations" where
  "identity_declarations = \<lparr>declared_producers = {|(12,view_identity,[view_output])|}, declared_consumers = {||},
    declared_sockets = {|(12,identity_socket_schema,2,False,view_identity,view_identity)|}\<rparr>"

definition comparison_declarations :: "(nat,nat,nat) resolution_declarations" where
  "comparison_declarations = \<lparr>declared_producers = {|(7,view_identity,[view_output])|}, declared_consumers = {||},
    declared_sockets = {|(7,comparison_socket_schema,0,False,view_identity,view_identity),
      (7,comparison_socket_schema,1,False,view_identity,view_identity),
      (7,comparison_socket_schema,2,False,view_identity,view_identity),
      (7,comparison_socket_schema,3,False,view_identity,view_identity)|}\<rparr>"

definition fields_admission_declarations :: "(nat,nat,nat) resolution_declarations" where
  "fields_admission_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(7,11,whole_view,0)|},
    declared_sockets = {||}\<rparr>"

definition headed_declarations :: "(nat,nat,nat) resolution_declarations" where
  "headed_declarations = \<lparr>declared_producers = {|(29,headed_fields_view,headed_fields_holes)|},
    declared_consumers = {|(37,29,view_swap,0)|},
    declared_sockets = {|(29,headed_socket_schema,5,False,view_identity,headed_fields_view),
      (29,headed_socket_schema,6,False,view_identity,headed_fields_view),
      (29,headed_socket_schema,7,False,view_identity,headed_fields_view)|}\<rparr>"

definition family_rows_declarations :: "(nat,nat,nat) resolution_declarations" where
  "family_rows_declarations = \<lparr>declared_producers = {||},
    declared_consumers = {|(37,32,rooted_artifact_view,0),(29,21,whole_view,0),(29,31,view_identity,0)|},
    declared_sockets = {|(32,family_rows_socket_schema,0,False,headed_incidence_view,view_identity)|}\<rparr>"

definition record_artifact_declarations :: "(nat,nat,nat) resolution_declarations" where
  "record_artifact_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(37,34,rooted_artifact_view,0)|},
    declared_sockets = {||}\<rparr>"

definition target_artifact_declarations :: "(nat,nat,nat) resolution_declarations" where
  "target_artifact_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(37,35,view_swap,0)|},
    declared_sockets = {||}\<rparr>"

definition admission_declarations :: "(nat,nat,nat) resolution_declarations" where
  "admission_declarations = \<lparr>declared_producers = {|(36,inner_right_view,[snd (snd inner_right_view)])|},
    declared_consumers = {|(37,36,rooted_artifact_view,0)|},
    declared_sockets = {|(36,external_socket_schema,5,False,view_identity,inner_right_view)|}\<rparr>"

definition reading_declarations :: "(nat,nat,nat) resolution_declarations" where
  "reading_declarations = \<lparr>declared_producers = {|(42,outer_pair_view,outer_pair_holes)|}, declared_consumers = {||},
    declared_sockets = {||}\<rparr>"

definition location_declarations :: "(nat,nat,nat) resolution_declarations" where
  "location_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(42,41,citation_field_view,0)|},
    declared_sockets = {||}\<rparr>"

definition resolution_site_declarations :: "(nat,nat,nat) resolution_declarations" where
  "resolution_site_declarations = \<lparr>declared_producers = {|(39,outer_pair_view,[snd (snd outer_pair_view)])|},
    declared_consumers = {||}, declared_sockets = {||}\<rparr>"

definition interpretation_declarations :: "(nat,nat,nat) resolution_declarations" where
  "interpretation_declarations = \<lparr>declared_producers = {|(40,inner_right_view,[snd (snd inner_right_view)])|},
    declared_consumers = {||},
    declared_sockets = {|(40,interpretation_socket_schema,0,False,outer_pair_view,inner_right_view)|}\<rparr>"

definition projection_target_declarations :: "(nat,nat,nat) resolution_declarations" where
  "projection_target_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(40,45,view_identity,0)|},
    declared_sockets = {||}\<rparr>"

definition binder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "binder_declarations = \<lparr>declared_producers = {|(54,view_identity,[view_output])|},
    declared_consumers = {|(37,54,rooted_artifact_view,0)|},
    declared_sockets = {|(54,binder_socket_schema,1,False,view_identity,view_identity)|}\<rparr>"

definition bag_binder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "bag_binder_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(54,6,view_swap,0)|},
    declared_sockets = {||}\<rparr>"

definition union_binder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "union_binder_declarations = \<lparr>declared_producers = {||},
    declared_consumers = {|(54,48,view_swap,0),(54,48,middle_view,0)|}, declared_sockets = {||}\<rparr>"

definition instantiation_binder_declarations :: "(nat,nat,nat) resolution_declarations" where
  "instantiation_binder_declarations = \<lparr>declared_producers = {||}, declared_consumers = {|(54,55,scope_view,0)|},
    declared_sockets = {||}\<rparr>"

lemmas artifact_citation_views_formed = view_identity_formed view_swap_formed lookup_view_formed
  inner_right_view_formed outer_pair_view_formed headed_fields_view_formed rooted_artifact_view_formed
  whole_view_formed citation_field_view_formed middle_view_formed scope_view_formed headed_incidence_view_formed

lemmas discharged_unfold = declarations_discharged_def declarations_formed_def artifact_citation_views_formed

theorem lookup_declarations_discharged:
  "declarations_discharged (positive_meaning artifact_lookup_system) lookup_declarations
    artifact_citation_correspondence"
  using lookup_producer_discharged lookup_socket_discharged
  by (simp add: discharged_unfold lookup_declarations_def)

theorem identity_declarations_discharged:
  "declarations_discharged (positive_meaning artifact_identity_system) identity_declarations
    artifact_citation_correspondence"
  using identity_producer_discharged identity_socket_discharged
  by (simp add: discharged_unfold identity_declarations_def)

theorem comparison_declarations_discharged:
  "declarations_discharged (positive_meaning artifact_comparison_system) comparison_declarations
    artifact_citation_correspondence"
  using comparison_producer_discharged comparison_socket_discharged[of 0] comparison_socket_discharged[of 1]
    comparison_socket_discharged[of 2] comparison_socket_discharged[of 3]
  by (simp add: discharged_unfold comparison_declarations_def)

theorem fields_admission_declarations_discharged:
  "declarations_discharged (positive_meaning artifact_admission_system) fields_admission_declarations
    artifact_citation_correspondence"
  using admission_fields_consumer by (simp add: discharged_unfold fields_admission_declarations_def)

theorem headed_declarations_discharged:
  "declarations_discharged (positive_meaning headed_material_system) headed_declarations
    artifact_citation_correspondence"
  using headed_producer_discharged headed_artifact_consumer headed_socket_discharged[of 5]
    headed_socket_discharged[of 6] headed_socket_discharged[of 7]
  by (simp add: discharged_unfold headed_declarations_def)

theorem family_rows_declarations_discharged:
  "declarations_discharged (positive_meaning family_admission_system) family_rows_declarations
    artifact_citation_correspondence"
  using family_artifact_consumer keyed_rows_consumer sockets_rows_consumer family_rows_socket_discharged
  by (simp add: discharged_unfold family_rows_declarations_def)

theorem record_artifact_declarations_discharged:
  "declarations_discharged (positive_meaning record_admission_system) record_artifact_declarations
    artifact_citation_correspondence"
  using record_artifact_consumer by (simp add: discharged_unfold record_artifact_declarations_def)

theorem target_artifact_declarations_discharged:
  "declarations_discharged (positive_meaning target_admission_system) target_artifact_declarations
    artifact_citation_correspondence"
  using target_artifact_consumer by (simp add: discharged_unfold target_artifact_declarations_def)

theorem admission_declarations_discharged:
  "declarations_discharged (positive_meaning citation_admission_system) admission_declarations
    artifact_citation_correspondence"
  using admission_producer_discharged admission_artifact_consumer external_socket_discharged
  by (simp add: discharged_unfold admission_declarations_def)

theorem reading_declarations_discharged:
  "declarations_discharged (positive_meaning citation_reading_system) reading_declarations
    artifact_citation_correspondence"
  using reading_producer_discharged
  by (simp add: discharged_unfold reading_declarations_def)

theorem location_declarations_discharged:
  "declarations_discharged (positive_meaning citation_location_system) location_declarations
    artifact_citation_correspondence"
  using location_citation_consumer by (simp add: discharged_unfold location_declarations_def)

theorem resolution_site_declarations_discharged:
  "declarations_discharged (positive_meaning citation_resolution_system) resolution_site_declarations
    artifact_citation_correspondence"
  using resolution_producer_discharged by (simp add: discharged_unfold resolution_site_declarations_def)

theorem interpretation_declarations_discharged:
  "declarations_discharged (positive_meaning citation_interpretation_system) interpretation_declarations
    artifact_citation_correspondence"
  using interpretation_producer_discharged interpretation_socket_discharged
  by (simp add: discharged_unfold interpretation_declarations_def)

theorem projection_target_declarations_discharged:
  "declarations_discharged (positive_meaning target_projection_system) projection_target_declarations
    artifact_citation_correspondence"
  using projection_target_consumer by (simp add: discharged_unfold projection_target_declarations_def)

theorem binder_declarations_discharged:
  "declarations_discharged (positive_meaning binder_admission_system) binder_declarations
    artifact_citation_correspondence"
  using binder_producer_discharged binder_artifact_consumer binder_socket_discharged
  by (simp add: discharged_unfold binder_declarations_def)

theorem bag_binder_declarations_discharged:
  "declarations_discharged (positive_meaning bag_comparison_system) bag_binder_declarations
    artifact_citation_correspondence"
  using bag_binders_consumer by (simp add: discharged_unfold bag_binder_declarations_def)

theorem union_binder_declarations_discharged:
  "declarations_discharged (positive_meaning data_union_system) union_binder_declarations
    artifact_citation_correspondence"
  using union_left_consumer union_middle_consumer by (simp add: discharged_unfold union_binder_declarations_def)

theorem instantiation_binder_declarations_discharged:
  "declarations_discharged (positive_meaning pattern_instantiation_system) instantiation_binder_declarations
    artifact_citation_correspondence"
  using instantiation_scope_consumer by (simp add: discharged_unfold instantiation_binder_declarations_def)

end
