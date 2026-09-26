theory Factor_Root_Family_Declarations
  imports Development_Given_Declarations Factor_Resolution_Carriers Factor_Package_Membership Factor_Package_Additions
begin

text \<open>
  The root family's declarations (R6b of DECISIONS.md "The native evaluator constructs the missing witnesses by
  resolution", its addition "The given's remaining producers: views, carriers and narrowed sockets", the root-family
  part): 79 declared a producer at the view Pair ((e,u),r) w, its consumers 77 (at 80's clause) and 47 (at 392's and
  525's, under the bound), the kept socket at 83.0/1 with 5 a carrier, and the free socket 32 at 79.0/1 with its
  inputs (correction (9)). Each obligation is discharged at the system where its clauses stand, from the notion's
  exact contract: nothing is proved again of a notion's meaning, and no clause of any program changes.
\<close>

section \<open>The classes and correspondences the root family's outputs carry\<close>

text \<open>
  79's output is a bag of definition sites: every order of the family's destinations, a destination repeated at
  distinct sockets kept. Two outputs correspond when they present one bag (@{text root_family_correspondence}). A
  carrier's outputs are data lists permuted (@{text term_bag_transport}).
\<close>

lemma data_bag_function:
  "data_bag_presents (\<lambda>a t. t = f a) N t \<longleftrightarrow> (\<exists>xs. mset xs = N \<and> t = data_list_term (map f xs))"
  by (auto simp: data_bag_presents_def data_sequence_presents_def list_all2_function)


abbreviation site_bag_presents :: "local_address option definition_site multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "site_bag_presents \<equiv> data_bag_presents (\<lambda>d t. t = definition_site_value d)"

lemma site_bag_presents_sites:
  "site_bag_presents N t \<longleftrightarrow> (\<exists>ds. mset ds = N \<and> t = data_list_term (map (\<lambda>d. definition_site_value d) ds))"
  by (simp only: data_bag_function)

lemma site_bag_presentation_class:
  "presentation_class site_bag_presents (\<lambda>_. True) (\<lambda>t. \<exists>N. site_bag_presents N t)"
proof -
  have element: "presentation_class (\<lambda>d t. t = definition_site_value d) (\<lambda>_. True) (\<lambda>p. \<exists>a. p = definition_site_value a)"
    using injective_presentation_class[of "\<lambda>d. definition_site_value d" "\<lambda>_. True"] definition_site_value_injective
    by simp
  show ?thesis using presentation_class.recovered_admission[OF data_bag_presentation_class[OF element]] by simp
qed

definition root_family_correspondence :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "root_family_correspondence = presentation_transport site_bag_presents site_bag_presents"

definition root_family_correspondences :: "nat \<Rightarrow> nat \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "root_family_correspondences d = (\<lambda>i. if d = 79 then root_family_correspondence else (=))"

lemma root_family_correspondences_root: "root_family_correspondences 79 = (\<lambda>i. root_family_correspondence)"
  by (simp add: root_family_correspondences_def)

abbreviation term_bag_presents :: "factor_term multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_bag_presents \<equiv> data_bag_presents (\<lambda>a t. t = a)"

lemma term_bag_presents_terms: "term_bag_presents N t \<longleftrightarrow> (\<exists>ys. mset ys = N \<and> t = data_list_term ys)"
  using data_bag_function[of "\<lambda>a. a"] by simp

lemma term_bag_presentation_class:
  "presentation_class term_bag_presents (\<lambda>_. True) (\<lambda>t. \<exists>N. term_bag_presents N t)"
  using presentation_class.recovered_admission[OF data_bag_presentation_class[OF identity_presentation_class]] by simp

abbreviation rows_formed :: "(factor_term \<times> factor_term) multiset \<Rightarrow> bool" where
  "rows_formed N \<equiv> \<forall>z\<in>#N. term_formed (fst z) \<and> term_formed (snd z)"

abbreviation row_bag_presents :: "(factor_term \<times> factor_term) multiset \<Rightarrow> factor_term \<Rightarrow> bool" where
  "row_bag_presents \<equiv> data_bag_presents
    (\<lambda>z t. term_formed (fst z) \<and> term_formed (snd z) \<and> t = Pair_Term (fst z) (snd z))"

lemma list_all2_rows:
  "list_all2 (\<lambda>z t. term_formed (fst z) \<and> term_formed (snd z) \<and> t = Pair_Term (fst z) (snd z)) xs ps \<longleftrightarrow>
    ps = map (\<lambda>(k,v). Pair_Term k v) xs \<and> (\<forall>(k,v)\<in>set xs. term_formed k \<and> term_formed v)"
  by (induction xs arbitrary: ps) (auto simp: list_all2_Cons1)

lemma row_bag_presents_rows:
  "row_bag_presents N t \<longleftrightarrow> (\<exists>zs. mset zs = N \<and> term_formed (pair_list_term zs) \<and> t = pair_list_term zs)"
  by (auto simp: data_bag_presents_def data_sequence_presents_def list_all2_rows pair_list_term_formed_iff)

lemma row_bag_presentation_class:
  "presentation_class row_bag_presents rows_formed (\<lambda>t. \<exists>N. row_bag_presents N t)"
proof -
  have inj: "inj_on (\<lambda>z. Pair_Term (fst z) (snd z)) {z. term_formed (fst z) \<and> term_formed (snd z)}"
    by (auto simp: inj_on_def prod_eq_iff)
  have element: "presentation_class (\<lambda>z t. term_formed (fst z) \<and> term_formed (snd z) \<and> t = Pair_Term (fst z) (snd z))
      (\<lambda>z. term_formed (fst z) \<and> term_formed (snd z))
      (\<lambda>p. \<exists>z. (term_formed (fst z) \<and> term_formed (snd z)) \<and> p = Pair_Term (fst z) (snd z))"
    using injective_presentation_class[OF inj] by (simp only: conj_assoc)
  show ?thesis using presentation_class.recovered_admission[OF data_bag_presentation_class[OF element]] by simp
qed

abbreviation row_bag_transport :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "row_bag_transport \<equiv> presentation_transport row_bag_presents row_bag_presents"

abbreviation term_bag_transport :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "term_bag_transport \<equiv> presentation_transport term_bag_presents term_bag_presents"

lemma term_bag_transport_iff:
  "term_bag_transport t t' \<longleftrightarrow> (\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> mset xs = mset xs')"
proof
  assume "term_bag_transport t t'"
  then obtain ys ys' where "t = data_list_term ys" "t' = data_list_term ys'" "mset ys = mset ys'"
    by (auto simp: presentation_transport_def term_bag_presents_terms)
  then show "\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> mset xs = mset xs'" by blast
next
  assume "\<exists>xs xs'. t = data_list_term xs \<and> t' = data_list_term xs' \<and> mset xs = mset xs'"
  then obtain xs xs' where "t = data_list_term xs" "t' = data_list_term xs'" "mset xs = mset xs'" by blast
  then show "term_bag_transport t t'" unfolding presentation_transport_def term_bag_presents_terms by blast
qed

lemma term_bag_transport_lists:
  "term_bag_transport (data_list_term xs) (data_list_term ys) \<longleftrightarrow> mset xs = mset ys"
  by (auto simp: term_bag_transport_iff data_list_term_injective)

lemma term_bag_transport_sym: "symp term_bag_transport"
  unfolding symp_def term_bag_transport_iff by metis

lemma root_family_correspondence_sites:
  assumes "root_family_correspondence y y'"
  obtains ds ds' where "y = data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    "y' = data_list_term (map (\<lambda>d. definition_site_value d) ds')" "mset ds = mset ds'"
  using assms by (auto simp: root_family_correspondence_def presentation_transport_def site_bag_presents_sites)

lemma root_family_correspondence_permuted:
  assumes "root_family_correspondence y y'"
  shows "term_bag_transport y y'"
proof -
  obtain ds ds' where y: "y = data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    and y': "y' = data_list_term (map (\<lambda>d. definition_site_value d) ds')" and m: "mset ds = mset ds'"
    by (rule root_family_correspondence_sites[OF assms])
  show ?thesis using m by (simp add: y y' term_bag_transport_lists)
qed

text \<open>A list read by a functional relation is the relation's function mapped over it.\<close>

lemma related_list_function:
  assumes related: "list_all2 R as ds" and functional: "\<And>a d d'. R a d \<Longrightarrow> R a d' \<Longrightarrow> d = d'"
  shows "ds = map (\<lambda>a. SOME d. R a d) as"
proof (rule nth_equalityI)
  have len: "length as = length ds" by (rule list_all2_lengthD[OF related])
  show "length ds = length (map (\<lambda>a. SOME d. R a d) as)" using len by simp
  fix i assume i: "i < length ds"
  have r: "R (as ! i) (ds ! i)" by (rule list_all2_nthD2[OF related i])
  have "R (as ! i) (SOME d. R (as ! i) d)" using r by (rule someI)
  then show "ds ! i = map (\<lambda>a. SOME d. R a d) as ! i" using functional[OF r] i len by simp
qed

section \<open>The views\<close>

text \<open>
  79's argument ((e,u),(r,w)) read as its input ((e,u),r) and its output w; 5's (x,(l,r)) as its input (x,l) and its
  remainder r.
\<close>

definition root_family_view :: "nat resolution_view" where
  "root_family_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    Finite_Variable 3)"

definition selection_view :: "nat resolution_view" where
  "selection_view = (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1), Finite_Variable 2)"

lemma root_family_view_formed: "view_formed root_family_view"
  by (auto simp: view_formed_def root_family_view_def)

lemma selection_view_formed: "view_formed selection_view"
  by (auto simp: view_formed_def selection_view_def)

lemma root_family_view_term:
  "resolution_view_term root_family_view (Pair_Term (Pair_Term e u) (Pair_Term r w)) = Some (Pair_Term (Pair_Term e u) r,w)"
  by (simp add: resolution_view_term_def root_family_view_def view_lookup_def)

lemma selection_view_term:
  "resolution_view_term selection_view (Pair_Term m (Pair_Term l r)) = Some (Pair_Term m l,r)"
  by (simp add: resolution_view_term_def selection_view_def view_lookup_def)

lemma root_family_view_pattern:
  "resolution_view_pattern root_family_view (Finite_Pattern_Pair (Finite_Pattern_Pair a b) (Finite_Pattern_Pair c d)) =
    Some (Finite_Pattern_Pair (Finite_Pattern_Pair a b) c,d)"
  by (simp add: resolution_view_pattern_def root_family_view_def view_lookup_def)

lemma selection_view_pattern:
  "resolution_view_pattern selection_view (Finite_Pattern_Pair a (Finite_Pattern_Pair b c)) =
    Some (Finite_Pattern_Pair a b,c)"
  by (simp add: resolution_view_pattern_def selection_view_def view_lookup_def)


section \<open>(1) 79 a producer at its view\<close>

text \<open>
  Two answers at one ((e,u),r) read one environment, one artifact and one family (@{thm [source] family_at_unique});
  their socket enumerations are distinct lists of that one family, and each endpoint is located at one destination
  (@{thm [source] located_at_unique}), so the two outputs list one bag of definition sites.
\<close>

theorem root_family_producer_discharged:
  "producer_discharged (positive_meaning root_family_reading_system) 79 root_family_view
    [snd (snd root_family_view)] (\<lambda>i. root_family_correspondence)"
  unfolding producer_discharged_single
proof (intro allI impI)
  fix a b u v v'
  assume a: "(79,a) \<in> positive_meaning root_family_reading_system"
    and b: "(79,b) \<in> positive_meaning root_family_reading_system"
    and va: "resolution_view_term root_family_view a = Some (u,v)"
    and vb: "resolution_view_term root_family_view b = Some (u,v')"
  obtain E e w r R xs ds where pa: "a = citation_observation_argument e (use_data_term w) (Payload_Term r)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds))"
    "environment_value_presents E e" "artifact_at E w R" "distinct xs" "family_at R r (set xs)"
    "list_all2 (\<lambda>x d. located_at E w x (fst d) (snd d)) (map snd xs) ds"
    using a by (simp only: root_family_reading_exact) blast
  obtain E' e' w' r' R' xs' ds' where pb: "b = citation_observation_argument e' (use_data_term w') (Payload_Term r')
      (data_list_term (map (\<lambda>d. definition_site_value d) ds'))"
    "environment_value_presents E' e'" "artifact_at E' w' R'" "distinct xs'" "family_at R' r' (set xs')"
    "list_all2 (\<lambda>x d. located_at E' w' x (fst d) (snd d)) (map snd xs') ds'"
    using b by (simp only: root_family_reading_exact) blast
  have ua: "u = Pair_Term (Pair_Term e (use_data_term w)) (Payload_Term r)"
    and v: "v = data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    using va by (simp_all add: pa(1) root_family_view_term)
  have ub: "u = Pair_Term (Pair_Term e' (use_data_term w')) (Payload_Term r')"
    and v': "v' = data_list_term (map (\<lambda>d. definition_site_value d) ds')"
    using vb by (simp_all add: pb(1) root_family_view_term)
  have same: "e' = e" "w' = w" "r' = r" using ua ub by (simp_all add: inj_eq[OF use_data_term_injective])
  have E: "E' = E" by (rule environment_value_presents_unique[OF pb(2)[unfolded same] pa(2)])
  have ef: "environment_formed E" using environment_value_presents_formed[OF pa(2)] by blast
  have R: "R = R'" by (rule environment_artifact_unique[OF ef pa(3) pb(3)[unfolded E same]])
  have sets: "set xs' = set xs" by (rule family_at_unique[OF pb(5)[unfolded same R[symmetric]] pa(5)])
  have ms: "mset xs' = mset xs" using set_eq_iff_mset_eq_distinct[OF pb(4) pa(4)] sets by simp
  have functional: "d = d'" if "located_at E w x (fst d) (snd d)" "located_at E w x (fst d') (snd d')" for x d d'
    using located_at_unique[OF ef that] by (simp add: prod_eq_iff)
  let ?f = "\<lambda>x. SOME d. located_at E w x (fst d) (snd d)"
  have da: "ds = map ?f (map snd xs)" by (rule related_list_function[OF pa(6) functional])
  have db: "ds' = map ?f (map snd xs')" by (rule related_list_function[OF pb(6)[unfolded E same] functional])
  have "mset ds = mset ds'" by (simp add: da db ms)
  then show "root_family_correspondence v v'"
    unfolding root_family_correspondence_def presentation_transport_def site_bag_presents_sites
    using v v' by blast
qed

section \<open>(2) Its consumers, derived from the clauses that hold its output\<close>

text \<open>
  At 80's clause 79's output w is held by 77 at the right of its argument; at 392's and 525's (both
  @{const package_additions_schema}), 79's output x4 is held by 47 at the left, under the bound x5; at 83's first
  clause it is held by 5 (the kept socket below).
\<close>

lemma root_family_holders:
  "(0,79,citation_observation_pattern data_x data_y data_z data_w) \<in> schema_premises package_admission_schema"
  "(1,77,Pattern_Pair data_x data_w) \<in> schema_premises package_admission_schema"
  "(2,79,Pattern_Pair (Pattern_Pair data_y data_z) (Pattern_Pair data_w (Pattern_Variable 4)))
    \<in> schema_premises (package_additions_schema l)"
  "(3,47,Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)) \<in> schema_premises (package_additions_schema l)"
  "(1,79,citation_observation_pattern data_x data_y data_z (Pattern_Variable 4)) \<in> schema_premises package_membership_root_schema"
  "(2,5,Pattern_Pair data_w (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5))) \<in> schema_premises package_membership_root_schema"
  by (simp_all add: package_admission_schema_def package_additions_schema_def package_membership_root_schema_def)

lemma closure_admission_sites:
  "(77,Pair_Term x (data_list_term (map (\<lambda>d. definition_site_value d) ds))) \<in> positive_meaning package_closure_admission_system
    \<longleftrightarrow> (\<exists>E. environment_value_presents E x \<and> native_package_formed E (set ds))"
  by (simp only: package_closure_admission_exact factor_term.inject data_list_term_injective
    injective_mapped_lists[OF definition_site_value_injective]) blast

theorem root_family_closure_consumer:
  "consumer_discharged (positive_meaning package_closure_admission_system) 77 view_identity root_family_correspondence"
  unfolding consumer_view_simps(1)[symmetric] consumer_discharged_argument consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "root_family_correspondence y y'"
  then obtain ds ds' where y: "y = data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    and y': "y' = data_list_term (map (\<lambda>d. definition_site_value d) ds')" and m: "mset ds = mset ds'"
    by (rule root_family_correspondence_sites)
  show "(77,Pair_Term x y) \<in> positive_meaning package_closure_admission_system \<longleftrightarrow>
      (77,Pair_Term x y') \<in> positive_meaning package_closure_admission_system"
    by (simp only: y y' closure_admission_sites mset_eq_setD[OF m])
qed

lemma subset_left_set:
  assumes "set as = set bs"
  shows "(47,Pair_Term (data_list_term as) x) \<in> positive_meaning data_subset_system \<longleftrightarrow>
    (47,Pair_Term (data_list_term bs) x) \<in> positive_meaning data_subset_system"
  using assms by (simp add: data_subset_exact data_list_term_injective)

theorem root_family_bound_consumer:
  "consumer_discharged (positive_meaning data_subset_system) 47 view_swap root_family_correspondence"
  unfolding consumer_view_simps(2)[symmetric] consumer_discharged_argument consumer_argument_def if_False
proof (intro allI impI)
  fix x y y' assume "root_family_correspondence y y'"
  then obtain ds ds' where y: "y = data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    and y': "y' = data_list_term (map (\<lambda>d. definition_site_value d) ds')" and m: "mset ds = mset ds'"
    by (rule root_family_correspondence_sites)
  have "set (map (\<lambda>d. definition_site_value d) ds) = set (map (\<lambda>d. definition_site_value d) ds')"
    using mset_eq_setD[OF m] by simp
  then show "(47,Pair_Term y x) \<in> positive_meaning data_subset_system \<longleftrightarrow>
      (47,Pair_Term y' x) \<in> positive_meaning data_subset_system"
    unfolding y y' by (rule subset_left_set)
qed

section \<open>(3) The kept socket at 83.0/1, 5 a carrier\<close>

text \<open>
  5 selects a member of 79's output and returns the remainder, which no other goal holds: a permuted list gives the
  member at another position and a permuted remainder (@{thm [source] data_selection_exact}).
\<close>

definition selection_input :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "selection_input x x' \<longleftrightarrow> (\<exists>m l l'. x = Pair_Term m l \<and> x' = Pair_Term m l' \<and> term_bag_transport l l')"

theorem selection_carrier:
  "carrier_discharged (positive_meaning bag_comparison_system) 5 selection_view selection_input term_bag_transport"
  unfolding carrier_discharged_def
proof (intro allI impI)
  fix a x y x'
  assume holds: "(5,a) \<in> positive_meaning bag_comparison_system"
    and va: "resolution_view_term selection_view a = Some (x,y)" and c: "selection_input x x'"
  obtain m pre post where a: "a = Pair_Term m (Pair_Term (data_list_term (pre@m#post)) (data_list_term (pre@post)))"
    and el: "data_elements (pre@m#post)"
    using data_selection_sound[OF holds] by auto
  have x: "x = Pair_Term m (data_list_term (pre@m#post))" and y: "y = data_list_term (pre@post)"
    using va by (simp_all add: a selection_view_term)
  obtain ls' where x': "x' = Pair_Term m (data_list_term ls')" and ml: "mset ls' = mset (pre@m#post)"
    using c by (auto simp: x selection_input_def term_bag_transport_iff data_list_term_injective)
  have "m \<in> set ls'" using mset_eq_setD[OF ml] by simp
  then obtain pre' post' where ls': "ls' = pre'@m#post'" by (meson split_list)
  have el': "data_elements ls'" using el by (simp add: mset_eq_setD[OF ml])
  have b: "(5,Pair_Term m (Pair_Term (data_list_term ls') (data_list_term (pre'@post')))) \<in> positive_meaning bag_comparison_system"
    using el' ls' by (simp only: data_selection_exact) blast
  have "mset (pre@post) = mset (pre'@post')" using ml ls' by simp
  then show "\<exists>b y'. (5,b) \<in> positive_meaning bag_comparison_system \<and>
      resolution_view_term selection_view b = Some (x',y') \<and> term_bag_transport y y'"
    using b by (intro exI[of _ "Pair_Term m (Pair_Term (data_list_term ls') (data_list_term (pre'@post')))"]
      exI[of _ "data_list_term (pre'@post')"] conjI) (simp_all add: x' y selection_view_term term_bag_transport_lists)
qed

definition membership_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "membership_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2)) (Finite_Variable 3),
    finite_schema_premises = {|(0,80,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2)),
      (1,79,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4))),
      (2,5,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)))|},
    finite_schema_materials = {||}\<rparr>"

lemma membership_socket_decoded: "decode_finite_schema membership_socket_schema = package_membership_root_schema"
  by (simp add: membership_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def package_membership_root_schema_def)

lemma relation_option_single:
  assumes "\<And>v'. (k,v') |\<in>| R \<longleftrightarrow> v' = v"
  shows "finite_relation_option R k = Some v"
proof -
  have "fimage snd (ffilter (\<lambda>r. fst r = k) R) = {|v|}" using assms by (force simp: fset_eq_iff)
  then show ?thesis by (simp add: finite_relation_option_def)
qed

lemma membership_socket_premises:
  "finite_relation_option (finite_schema_premises membership_socket_schema) 1 =
    Some (79,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4)))"
  "finite_relation_option (finite_schema_premises membership_socket_schema) 2 =
    Some (5,Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)))"
  by (rule relation_option_single, auto simp: membership_socket_schema_def)+

definition membership_carriers :: "nat clause_carrier list" where
  "membership_carriers = [(2,selection_view,selection_input,term_bag_transport)]"

lemma membership_socket_parts:
  "premise_parts membership_socket_schema 1 root_family_view =
    Some (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),Finite_Variable 4)"
  "premise_parts membership_socket_schema 2 selection_view =
    Some (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4),Finite_Variable 5)"
  by (simp_all only: premise_parts_at[OF membership_socket_premises(1)] premise_parts_at[OF membership_socket_premises(2)]
    root_family_view_pattern selection_view_pattern)

lemma membership_carried:
  "carried_variables membership_socket_schema 1 root_family_view membership_carriers = {4,5}"
  unfolding carried_variables_def membership_socket_parts(1)
  by (auto simp: membership_carriers_def membership_socket_parts(2) output_variables_def)

lemma membership_carried_before:
  "carried_variables membership_socket_schema 1 root_family_view (take 0 membership_carriers) = {4}"
  unfolding carried_variables_def membership_socket_parts(1) by (simp add: output_variables_def)

theorem membership_socket_carried:
  "socket_carried (positive_meaning package_membership_system) membership_socket_schema 1 True root_family_view
    view_identity root_family_correspondence membership_carriers"
proof -
  let ?M = "positive_meaning package_membership_system"
  have producer: "producer_discharged ?M 79 root_family_view [snd (snd root_family_view)] (\<lambda>_. root_family_correspondence)"
    using root_family_producer_discharged
    by (simp only: producer_discharged_site[of 79 ?M "positive_meaning root_family_reading_system",
      OF package_membership_components(2)])
  have carrier: "carrier_discharged ?M 5 selection_view selection_input term_bag_transport"
    using selection_carrier
    by (simp only: carrier_discharged_site[of 5 ?M "positive_meaning bag_comparison_system", OF package_membership_components(4)])
  have step: "carrier_step ?M membership_socket_schema 1 root_family_view root_family_correspondence membership_carriers 0"
    unfolding carrier_step_def
  proof (simp only: membership_carriers_def nth_Cons_0 prod.case membership_socket_premises(2) option.case
      selection_view_pattern, intro conjI selection_view_formed carrier output_covered_variable allI impI)
    show "fset (finite_pattern_variables (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))) \<inter>
        carried_variables membership_socket_schema 1 root_family_view [(2,selection_view,selection_input,term_bag_transport)]
      \<subseteq> carried_variables membership_socket_schema 1 root_family_view (take 0 [(2,selection_view,selection_input,term_bag_transport)])"
      using membership_carried[unfolded membership_carriers_def] membership_carried_before[unfolded membership_carriers_def]
      by simp
    show "fset (finite_pattern_variables (Finite_Variable 5)) \<inter>
        carried_variables membership_socket_schema 1 root_family_view (take 0 [(2,selection_view,selection_input,term_bag_transport)]) = {}"
      using membership_carried_before[unfolded membership_carriers_def] by simp
    fix g g'
    assume agree: "\<forall>v. v \<notin> carried_variables membership_socket_schema 1 root_family_view
        [(2,selection_view,selection_input,term_bag_transport)] \<longrightarrow> g v = g' v"
      and corr: "carried_correspond membership_socket_schema 1 root_family_view root_family_correspondence
        (take 0 [(2,selection_view,selection_input,term_bag_transport)]) g g'"
    have three: "g 3 = g' 3" using agree membership_carried[unfolded membership_carriers_def] by auto
    have "root_family_correspondence (g 4) (g' 4)"
      using corr[unfolded carried_correspond_def membership_socket_parts(1)] by (simp add: output_corresponds_def)
    then have "term_bag_transport (g 4) (g' 4)" by (rule root_family_correspondence_permuted)
    then show "selection_input (evaluate_pattern g (decode_finite_pattern (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))))
        (evaluate_pattern g' (decode_finite_pattern (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4))))"
      using three by (auto simp: selection_input_def)
  qed
  show ?thesis
    unfolding socket_carried_def membership_carried membership_socket_premises(1)
    using meaning_answers_formed[of package_membership_system] producer step
    by (auto simp: root_family_view_pattern root_family_view_formed output_covered_variable
      membership_socket_decoded package_membership_root_schema_def membership_carriers_def head_apart_def
      membership_socket_schema_def consumer_view_simps(1)[symmetric] consumer_view_pattern less_Suc_eq)
qed

theorem membership_socket_discharged:
  "socket_discharged (positive_meaning package_membership_system) membership_socket_schema 1 True root_family_view
    view_identity"
  by (rule socket_discharged_carried[OF membership_socket_carried])

section \<open>(4) The free socket 32 at 79.0/1 and its inputs\<close>

text \<open>
  79's clause as a finite schema, and the inputs of its socket 1 read at 32's view and 79's: 32's premise input
  (x4,x2) and 79's head input ((x0,x1),x2). Premise 0's variables (37's: x0, x1, x4) are among them, so the test as
  correction (9) changes it commits 32 at 79.0/1 once 37 is closed; the socket's obligation is unchanged.
\<close>

definition root_family_socket_schema :: "(nat,nat,nat) finite_factor_schema" where
  "root_family_socket_schema = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 4))),
      (1,32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2)) (Finite_Variable 5)),
      (2,59,Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6)),
      (3,78,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 7)),
      (4,51,Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 6)),
      (5,59,Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 3))|},
    finite_schema_materials = {||}\<rparr>"

lemma root_family_socket_decoded: "decode_finite_schema root_family_socket_schema = root_family_reading_schema"
  by (simp add: root_family_socket_schema_def decode_finite_schema_def decode_finite_call_pattern_def
    map_relation_values_def root_family_reading_schema_def)

theorem root_family_socket_inputs:
  "socket_inputs view_identity root_family_view root_family_socket_schema 1 = {0,1,2,4}"
  unfolding socket_inputs_def head_inputs_def root_family_socket_schema_def
  by (auto simp: consumer_view_simps(1)[symmetric] consumer_view_pattern root_family_view_pattern)

text \<open>
  The clause's premises at their keys, and each read at the view its carrying reads: 32's at the identity, 59's at the
  identity, 51's at the swap (from the keys to the rows), 78's at the consumer's carrier view.
\<close>

lemma root_family_socket_premises:
  "finite_relation_option (finite_schema_premises root_family_socket_schema) 1 =
    Some (32,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2)) (Finite_Variable 5))"
  "finite_relation_option (finite_schema_premises root_family_socket_schema) 2 =
    Some (59,Finite_Pattern_Pair (Finite_Variable 5) (Finite_Variable 6))"
  "finite_relation_option (finite_schema_premises root_family_socket_schema) 3 =
    Some (78,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 7))"
  "finite_relation_option (finite_schema_premises root_family_socket_schema) 4 =
    Some (51,Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 6))"
  "finite_relation_option (finite_schema_premises root_family_socket_schema) 5 =
    Some (59,Finite_Pattern_Pair (Finite_Variable 7) (Finite_Variable 3))"
  by (rule relation_option_single, auto simp: root_family_socket_schema_def)+

lemma root_family_socket_parts:
  "premise_parts root_family_socket_schema 1 view_identity =
    Some (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2),Finite_Variable 5)"
  "premise_parts root_family_socket_schema 2 view_identity = Some (Finite_Variable 5,Finite_Variable 6)"
  "premise_parts root_family_socket_schema 4 view_swap = Some (Finite_Variable 6,Finite_Variable 7)"
  "premise_parts root_family_socket_schema 3 (consumer_carrier_view view_identity) =
    Some (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 7),
      Finite_Pattern_Payload [])"
  "premise_parts root_family_socket_schema 5 view_identity = Some (Finite_Variable 7,Finite_Variable 3)"
proof -
  show "premise_parts root_family_socket_schema 1 view_identity =
      Some (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2),Finite_Variable 5)"
    by (simp only: premise_parts_at[OF root_family_socket_premises(1)])
      (simp add: consumer_view_simps(1)[symmetric] consumer_view_pattern)
  show "premise_parts root_family_socket_schema 2 view_identity = Some (Finite_Variable 5,Finite_Variable 6)"
    by (simp only: premise_parts_at[OF root_family_socket_premises(2)])
      (simp add: consumer_view_simps(1)[symmetric] consumer_view_pattern)
  show "premise_parts root_family_socket_schema 4 view_swap = Some (Finite_Variable 6,Finite_Variable 7)"
    by (simp only: premise_parts_at[OF root_family_socket_premises(4)])
      (simp add: consumer_view_simps(2)[symmetric] consumer_view_pattern)
  show "premise_parts root_family_socket_schema 3 (consumer_carrier_view view_identity) =
      Some (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 7),
        Finite_Pattern_Payload [])"
    by (simp only: premise_parts_at[OF root_family_socket_premises(3)])
      (simp add: consumer_carrier_view_def resolution_view_pattern_def view_identity_def identity_view_def view_lookup_def)
  show "premise_parts root_family_socket_schema 5 view_identity = Some (Finite_Variable 7,Finite_Variable 3)"
    by (simp only: premise_parts_at[OF root_family_socket_premises(5)])
      (simp add: consumer_view_simps(1)[symmetric] consumer_view_pattern)
qed

text \<open>
  78 holds the located rows at the right of its argument and checks every row: a permuted list is checked as the list
  is (@{thm [source] located_list_exact}), so 78 consumes the rows the keys carry.
\<close>

theorem located_rows_consumer:
  "consumer_discharged (positive_meaning located_list_system) 78 view_identity term_bag_transport"
  unfolding consumer_view_simps(1)[symmetric] consumer_discharged_argument consumer_argument_def if_True
proof (intro allI impI)
  fix x y y' assume "term_bag_transport y y'"
  then obtain ys ys' where y: "y = data_list_term ys" and y': "y' = data_list_term ys'" and m: "mset ys = mset ys'"
    by (auto simp: term_bag_transport_iff)
  show "(78,Pair_Term x y) \<in> positive_meaning located_list_system \<longleftrightarrow>
      (78,Pair_Term x y') \<in> positive_meaning located_list_system"
    by (simp add: y y' located_list_exact data_list_term_injective mset_eq_setD[OF m])
qed

text \<open>
  A list of keys permuted from a row list's keys is the keys of the rows permuted so (51 read from its keys to its
  rows).
\<close>

lemma keyed_list_permutation:
  assumes "mset ks = mset (map fst zs)"
  shows "\<exists>zs'. map fst zs' = ks \<and> mset zs' = mset zs"
  using assms
proof (induction ks arbitrary: zs)
  case Nil
  then have "map fst zs = []" by (metis mset.simps(1) mset_zero_iff_right)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons k ks)
  have "k \<in> set (map fst zs)" using Cons.prems by (metis list.set_intros(1) mset_eq_setD)
  then obtain v where "(k,v) \<in> set zs" by auto
  then obtain pre post where split: "zs = pre @ (k,v) # post" by (meson split_list)
  have "mset ks = mset (map fst (pre @ post))" using Cons.prems split by simp
  then obtain zs'' where keys: "map fst zs'' = ks" and rows: "mset zs'' = mset (pre @ post)" using Cons.IH by blast
  show ?case using split keys rows by (intro exI[of _ "(k,v) # zs''"]) simp
qed

section \<open>(3) The free socket 32 at 79.0/1, carried by 59 and 51, consumed by 78, carried by 59 to w\<close>

text \<open>
  The classes the carrying reads: a row list presents the bag of its formed rows, a term list the bag of its terms.
  59 is a function witness from rows to their values (@{thm [source] row_values_exact}), 51 one from rows to their
  keys (@{thm [source] row_keys_exact}), read against its direction along the keys: every key list presenting a row
  bag's keys is the keys of some presentation of that bag (@{thm [source] keyed_list_permutation}).
\<close>

theorem row_values_witness:
  "presented_function_witness row_bag_presents rows_formed (\<lambda>t. \<exists>N. row_bag_presents N t)
    term_bag_presents (\<lambda>_. True) (\<lambda>t. \<exists>N. term_bag_presents N t) (image_mset snd)
    (\<lambda>p q. (59,Pair_Term p q) \<in> positive_meaning row_values_system)"
proof (rule presented_function_witness.intro[OF row_bag_presentation_class term_bag_presentation_class]; unfold_locales)
  fix p q assume "(59,Pair_Term p q) \<in> positive_meaning row_values_system"
  then show "\<exists>N. row_bag_presents N p" by (auto simp: row_values_exact row_bag_presents_rows)
next
  fix a p q assume "row_bag_presents a p" and holds: "(59,Pair_Term p q) \<in> positive_meaning row_values_system"
  then obtain zs where zs: "mset zs = a" "p = pair_list_term zs" by (auto simp: row_bag_presents_rows)
  have "q = data_list_term (map snd zs)" using holds by (simp add: zs(2) row_values_at_rows)
  then show "term_bag_presents (image_mset snd a) q" using zs(1) unfolding term_bag_presents_terms
    by (intro exI[of _ "map snd zs"]) simp
next
  fix p assume "\<exists>N. row_bag_presents N p"
  then show "\<exists>q. (59,Pair_Term p q) \<in> positive_meaning row_values_system"
    by (auto simp: row_bag_presents_rows row_values_at_rows)
qed

theorem row_keys_witness:
  "presented_function_witness row_bag_presents rows_formed (\<lambda>t. \<exists>N. row_bag_presents N t)
    term_bag_presents (\<lambda>_. True) (\<lambda>t. \<exists>N. term_bag_presents N t) (image_mset fst)
    (\<lambda>p q. (51,Pair_Term p q) \<in> positive_meaning row_keys_system)"
proof (rule presented_function_witness.intro[OF row_bag_presentation_class term_bag_presentation_class]; unfold_locales)
  fix p q assume "(51,Pair_Term p q) \<in> positive_meaning row_keys_system"
  then show "\<exists>N. row_bag_presents N p" by (auto simp: row_keys_exact row_bag_presents_rows)
next
  fix a p q assume "row_bag_presents a p" and holds: "(51,Pair_Term p q) \<in> positive_meaning row_keys_system"
  then obtain zs where zs: "mset zs = a" "p = pair_list_term zs" by (auto simp: row_bag_presents_rows)
  have "q = data_list_term (map fst zs)" using holds by (simp add: zs(2) row_keys_at_rows)
  then show "term_bag_presents (image_mset fst a) q" using zs(1) unfolding term_bag_presents_terms
    by (intro exI[of _ "map fst zs"]) simp
next
  fix p assume "\<exists>N. row_bag_presents N p"
  then show "\<exists>q. (51,Pair_Term p q) \<in> positive_meaning row_keys_system"
    by (auto simp: row_bag_presents_rows row_keys_at_rows)
qed

lemma row_keys_along:
  assumes rows: "row_bag_presents a q" and keys: "term_bag_presents (image_mset fst a) p'"
  shows "\<exists>q'. row_bag_presents a q' \<and> (51,Pair_Term q' p') \<in> positive_meaning row_keys_system"
proof -
  obtain zs where zs: "mset zs = a" "term_formed (pair_list_term zs)" "q = pair_list_term zs"
    using rows by (auto simp: row_bag_presents_rows)
  obtain ks where ks: "mset ks = image_mset fst a" "p' = data_list_term ks" using keys by (auto simp: term_bag_presents_terms)
  obtain zs' where zs': "map fst zs' = ks" "mset zs' = mset zs"
    using keyed_list_permutation[of ks zs] ks(1) zs(1) by auto
  have formed: "term_formed (pair_list_term zs')" using zs(2) by (simp add: pair_list_term_formed_iff mset_eq_setD[OF zs'(2)])
  show ?thesis using zs zs' formed
    by (intro exI[of _ "pair_list_term zs'"]) (auto simp: row_bag_presents_rows row_keys_at_rows ks(2))
qed

theorem row_values_carrier:
  "carrier_discharged (positive_meaning row_values_system) 59 view_identity row_bag_transport term_bag_transport"
  by (rule function_witness_carrier[OF row_values_witness]) (auto simp: view_identity_term pair_view_some)

theorem row_keys_carrier:
  "carrier_discharged (positive_meaning row_keys_system) 51 view_swap term_bag_transport row_bag_transport"
  by (rule witness_along_carrier[OF row_keys_witness row_keys_along]) (auto simp: view_swap_term swap_view_some)

lemma row_bag_transport_permuted:
  assumes "row_bag_transport y y'"
  shows "term_bag_transport y y'"
proof -
  obtain N where "row_bag_presents N y" "row_bag_presents N y'" using assms by (auto simp: presentation_transport_def)
  then obtain zs zs' where "y = pair_list_term zs" "y' = pair_list_term zs'" "mset zs = mset zs'"
    by (auto simp: row_bag_presents_rows)
  then show ?thesis by (simp add: term_bag_transport_lists)
qed

theorem located_rows_bag_consumer:
  "consumer_discharged (positive_meaning located_list_system) 78 view_identity row_bag_transport"
  using located_rows_consumer row_bag_transport_permuted unfolding consumer_discharged_def by blast

lemma row_bag_transport_sym: "symp row_bag_transport"
  unfolding symp_def presentation_transport_def by blast

text \<open>
  32's producer at its rows' formed family correspondence: R6's discharge (@{thm [source] family_producer_discharged}),
  its answers formed, so the rows it answers are formed row bags.
\<close>

definition family_rows_formed :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "family_rows_formed y y' \<longleftrightarrow> given_correspondence 32 y y' \<and> term_formed y \<and> term_formed y'"

theorem family_producer_formed:
  "producer_discharged (positive_meaning family_admission_system) 32 view_identity [view_output] (\<lambda>i. family_rows_formed)"
  unfolding producer_discharged_identity
proof (intro allI impI)
  fix x y y' assume a: "(32,Pair_Term x y) \<in> positive_meaning family_admission_system"
    and b: "(32,Pair_Term x y') \<in> positive_meaning family_admission_system"
  have "given_correspondence 32 y y'"
    using family_producer_discharged[unfolded producer_discharged_identity] a b by blast
  moreover have "term_formed (Pair_Term x y)" "term_formed (Pair_Term x y')"
    using meaning_answers_formed[of family_admission_system] a b by blast+
  ultimately show "family_rows_formed y y'" by (simp add: family_rows_formed_def)
qed

lemma family_rows_formed_bag:
  assumes corr: "family_rows_formed y y'"
  shows "row_bag_transport y y'"
proof -
  have c: "given_correspondence 32 y y'" and fy: "term_formed y" and fy': "term_formed y'"
    using corr by (simp_all add: family_rows_formed_def)
  obtain A where "family_rows_presents A y" "family_rows_presents A y'"
    using c by (auto simp: given_correspondence_def presentation_transport_def)
  then obtain xs xs' where xs: "distinct xs" "set xs = A" "y = data_list_term (map address_pair_data xs)"
    and xs': "distinct xs'" "set xs' = A" "y' = data_list_term (map address_pair_data xs')"
    by (auto simp: data_collection_presents_def list_all2_function)
  have m: "mset xs = mset xs'" using set_eq_iff_mset_eq_distinct[OF xs(1) xs'(1)] xs(2) xs'(2) by simp
  let ?r = "\<lambda>z::local_address \<times> octets. (Payload_Term (fst z),Payload_Term (snd z))"
  have rows: "data_list_term (map address_pair_data zs) = pair_list_term (map ?r zs)" for zs
    by (induction zs) (simp_all add: address_pair_data_def)
  have y1: "y = pair_list_term (map ?r xs)" and y2: "y' = pair_list_term (map ?r xs')"
    using xs(3) xs'(3) rows by simp_all
  have "row_bag_presents (mset (map ?r xs)) y"
    unfolding row_bag_presents_rows using fy y1 by (intro exI[of _ "map ?r xs"]) simp
  moreover have "row_bag_presents (mset (map ?r xs)) y'"
    unfolding row_bag_presents_rows using fy' y2 m by (intro exI[of _ "map ?r xs'"]) simp
  ultimately show ?thesis by (auto simp: presentation_transport_def)
qed

definition root_family_carriers :: "nat clause_carrier list" where
  "root_family_carriers = [(2,view_identity,row_bag_transport,term_bag_transport),
    (4,view_swap,term_bag_transport,row_bag_transport),
    (3,consumer_carrier_view view_identity,consumer_input view_identity row_bag_transport,(=)),
    (5,view_identity,row_bag_transport,term_bag_transport)]"

lemma root_family_carriers_nth:
  "root_family_carriers ! 0 = (2,view_identity,row_bag_transport,term_bag_transport)"
  "root_family_carriers ! 1 = (4,view_swap,term_bag_transport,row_bag_transport)"
  "root_family_carriers ! 2 = (3,consumer_carrier_view view_identity,consumer_input view_identity row_bag_transport,(=))"
  "root_family_carriers ! 3 = (5,view_identity,row_bag_transport,term_bag_transport)"
  by (simp_all add: root_family_carriers_def)

lemma root_family_carried:
  "carried_variables root_family_socket_schema 1 view_identity root_family_carriers = {3,5,6,7}"
  "carried_variables root_family_socket_schema 1 view_identity (take 0 root_family_carriers) = {5}"
  "carried_variables root_family_socket_schema 1 view_identity (take 1 root_family_carriers) = {5,6}"
  "carried_variables root_family_socket_schema 1 view_identity (take 2 root_family_carriers) = {5,6,7}"
  "carried_variables root_family_socket_schema 1 view_identity (take 3 root_family_carriers) = {5,6,7}"
  unfolding carried_variables_def root_family_socket_parts(1)
  by (auto simp: root_family_carriers_def root_family_socket_parts(2,3,4,5) output_variables_def)

lemma consumer_input_pair: "corr v v' \<Longrightarrow> consumer_input view_identity corr (Pair_Term u v) (Pair_Term u v')"
  unfolding consumer_input_def view_identity_term
  by (intro exI[of _ u] exI[of _ v] exI[of _ v'] exI[of _ "Pair_Term u v'"]) (simp add: pair_view_def)


lemma root_family_socket_views:
  "resolution_view_pattern view_identity (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable (4::nat)) (Finite_Variable 2))
    (Finite_Variable 5)) = Some (Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 2),Finite_Variable 5)"
  "resolution_view_pattern view_identity (Finite_Pattern_Pair (Finite_Variable (5::nat)) (Finite_Variable 6)) =
    Some (Finite_Variable 5,Finite_Variable 6)"
  "resolution_view_pattern view_swap (Finite_Pattern_Pair (Finite_Variable (7::nat)) (Finite_Variable 6)) =
    Some (Finite_Variable 6,Finite_Variable 7)"
  "resolution_view_pattern (consumer_carrier_view view_identity)
    (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1)) (Finite_Variable 7)) =
    Some (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 7),
      Finite_Pattern_Payload [])"
  "resolution_view_pattern view_identity (Finite_Pattern_Pair (Finite_Variable (7::nat)) (Finite_Variable 3)) =
    Some (Finite_Variable 7,Finite_Variable 3)"
  using root_family_socket_parts(1)[unfolded premise_parts_at[OF root_family_socket_premises(1)]]
    root_family_socket_parts(2)[unfolded premise_parts_at[OF root_family_socket_premises(2)]]
    root_family_socket_parts(3)[unfolded premise_parts_at[OF root_family_socket_premises(4)]]
    root_family_socket_parts(4)[unfolded premise_parts_at[OF root_family_socket_premises(3)]]
    root_family_socket_parts(5)[unfolded premise_parts_at[OF root_family_socket_premises(5)]]
  by simp_all

theorem root_family_socket_carried:
  "socket_carried (positive_meaning root_family_reading_system) root_family_socket_schema 1 False view_identity
    root_family_view family_rows_formed root_family_carriers"
proof -
  let ?M = "positive_meaning root_family_reading_system" and ?S = root_family_socket_schema
  have producer: "producer_discharged ?M 32 view_identity [snd (snd view_identity)] (\<lambda>_. family_rows_formed)"
    using family_producer_formed
    by (simp only: view_identity_output producer_discharged_site[of 32 ?M "positive_meaning family_admission_system",
      OF root_family_reading_components(2)])
  have valued: "carrier_discharged ?M 59 view_identity row_bag_transport term_bag_transport"
    using row_values_carrier
    by (simp only: carrier_discharged_site[of 59 ?M "positive_meaning row_values_system", OF root_family_reading_components(3)])
  have keys: "carrier_discharged ?M 51 view_swap term_bag_transport row_bag_transport"
    using row_keys_carrier
    by (simp only: carrier_discharged_site[of 51 ?M "positive_meaning row_keys_system", OF root_family_reading_components(5)])
  have "consumer_discharged ?M 78 view_identity row_bag_transport"
    using located_rows_bag_consumer
      consumer_discharged_site[of 78 ?M "positive_meaning located_list_system", OF root_family_reading_components(4)] by blast
  then have located: "carrier_discharged ?M 78 (consumer_carrier_view view_identity)
      (consumer_input view_identity row_bag_transport) (=)"
    by (simp only: consumer_discharged_carrier[OF view_identity_formed row_bag_transport_sym])
  have consumer_formed: "view_formed (consumer_carrier_view view_identity)"
    by (simp add: consumer_carrier_view_formed view_identity_formed)
  have step0: "carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers 0"
    unfolding carrier_step_def
  proof (simp only: root_family_carriers_nth(1) prod.case root_family_socket_premises(2) option.case
      root_family_socket_views(2), intro conjI view_identity_formed valued output_covered_variable allI impI)
    show "fset (finite_pattern_variables (Finite_Variable 5)) \<inter>
        carried_variables ?S 1 view_identity root_family_carriers
      \<subseteq> carried_variables ?S 1 view_identity (take 0 root_family_carriers)"
      by (simp only: root_family_carried(1,2)) simp
    show "fset (finite_pattern_variables (Finite_Variable 6)) \<inter>
        carried_variables ?S 1 view_identity (take 0 root_family_carriers) = {}"
      by (simp only: root_family_carried(2)) simp
    fix g g'
    assume corr: "carried_correspond ?S 1 view_identity family_rows_formed (take 0 root_family_carriers) g g'"
    have "family_rows_formed (g 5) (g' 5)"
      using corr[unfolded carried_correspond_def root_family_socket_parts(1)] by (simp add: output_corresponds_def)
    then show "row_bag_transport (evaluate_pattern g (decode_finite_pattern (Finite_Variable 5)))
        (evaluate_pattern g' (decode_finite_pattern (Finite_Variable 5)))"
      by (simp add: family_rows_formed_bag)
  qed
  have step1: "carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers 1"
    unfolding carrier_step_def
  proof (simp only: root_family_carriers_nth(2) prod.case root_family_socket_premises(4) option.case
      root_family_socket_views(3), intro conjI view_swap_formed keys output_covered_variable allI impI)
    show "fset (finite_pattern_variables (Finite_Variable 6)) \<inter>
        carried_variables ?S 1 view_identity root_family_carriers
      \<subseteq> carried_variables ?S 1 view_identity (take 1 root_family_carriers)"
      by (simp only: root_family_carried(1,3)) simp
    show "fset (finite_pattern_variables (Finite_Variable 7)) \<inter>
        carried_variables ?S 1 view_identity (take 1 root_family_carriers) = {}"
      by (simp only: root_family_carried(3)) simp
    fix g g'
    assume corr: "carried_correspond ?S 1 view_identity family_rows_formed (take 1 root_family_carriers) g g'"
    have "term_bag_transport (g 6) (g' 6)"
      using corr[unfolded carried_correspond_def root_family_socket_parts(1)]
      by (simp add: root_family_carriers_def root_family_socket_parts(2) output_corresponds_def)
    then show "term_bag_transport (evaluate_pattern g (decode_finite_pattern (Finite_Variable 6)))
        (evaluate_pattern g' (decode_finite_pattern (Finite_Variable 6)))" by simp
  qed
  have step2: "carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers 2"
    unfolding carrier_step_def
  proof (simp only: root_family_carriers_nth(3) prod.case root_family_socket_premises(3) option.case
      root_family_socket_views(4), intro conjI consumer_formed located consumer_carrier_covered allI impI)
    show "fset (finite_pattern_variables (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
          (Finite_Variable 7))) \<inter> carried_variables ?S 1 view_identity root_family_carriers
      \<subseteq> carried_variables ?S 1 view_identity (take 2 root_family_carriers)"
      by (simp only: root_family_carried(1,4)) auto
    show "fset (finite_pattern_variables (Finite_Pattern_Payload [])) \<inter>
        carried_variables ?S 1 view_identity (take 2 root_family_carriers) = {}"
      by simp
    fix g g'
    assume agree: "\<forall>v. v \<notin> carried_variables ?S 1 view_identity root_family_carriers \<longrightarrow> g v = g' v"
      and corr: "carried_correspond ?S 1 view_identity family_rows_formed (take 2 root_family_carriers) g g'"
    have same: "g' 0 = g 0" "g' 1 = g 1" using agree[unfolded root_family_carried(1)] by auto
    have "row_bag_transport (g 7) (g' 7)"
      using corr[unfolded carried_correspond_def root_family_socket_parts(1)]
      by (simp add: root_family_carriers_def root_family_socket_parts(2,3) output_corresponds_def)
    then have "consumer_input view_identity row_bag_transport (Pair_Term (Pair_Term (g 0) (g 1)) (g 7))
        (Pair_Term (Pair_Term (g 0) (g 1)) (g' 7))" by (rule consumer_input_pair)
    then show "consumer_input view_identity row_bag_transport
        (evaluate_pattern g (decode_finite_pattern (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0)
          (Finite_Variable 1)) (Finite_Variable 7))))
        (evaluate_pattern g' (decode_finite_pattern (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0)
          (Finite_Variable 1)) (Finite_Variable 7))))"
      using same by simp
  qed
  have step3: "carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers 3"
    unfolding carrier_step_def
  proof (simp only: root_family_carriers_nth(4) prod.case root_family_socket_premises(5) option.case
      root_family_socket_views(5), intro conjI view_identity_formed valued output_covered_variable allI impI)
    show "fset (finite_pattern_variables (Finite_Variable 7)) \<inter>
        carried_variables ?S 1 view_identity root_family_carriers
      \<subseteq> carried_variables ?S 1 view_identity (take 3 root_family_carriers)"
      by (simp only: root_family_carried(1,5)) simp
    show "fset (finite_pattern_variables (Finite_Variable 3)) \<inter>
        carried_variables ?S 1 view_identity (take 3 root_family_carriers) = {}"
      by (simp only: root_family_carried(5)) simp
    fix g g'
    assume corr: "carried_correspond ?S 1 view_identity family_rows_formed (take 3 root_family_carriers) g g'"
    have "row_bag_transport (g 7) (g' 7)"
      using corr[unfolded carried_correspond_def root_family_socket_parts(1)]
      by (simp add: root_family_carriers_def root_family_socket_parts(2,3,4) output_corresponds_def)
    then show "row_bag_transport (evaluate_pattern g (decode_finite_pattern (Finite_Variable 7)))
        (evaluate_pattern g' (decode_finite_pattern (Finite_Variable 7)))" by simp
  qed
  have steps: "\<forall>i<length root_family_carriers. carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers i"
  proof (intro allI impI)
    fix i assume "i < length root_family_carriers"
    then have "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by (simp add: root_family_carriers_def; presburger)
    then show "carrier_step ?M ?S 1 view_identity family_rows_formed root_family_carriers i"
      using step0 step1 step2 step3 by blast
  qed
  show ?thesis
    unfolding socket_carried_def root_family_carried(1) root_family_socket_premises(1) root_family_socket_views(1)
    using meaning_answers_formed[of root_family_reading_system] producer steps
    by (auto simp: view_identity_formed output_covered_variable root_family_socket_decoded root_family_reading_schema_def
      root_family_carriers_def head_apart_def root_family_socket_schema_def root_family_view_pattern
      root_family_socket_views(1))
qed

theorem root_family_socket_discharged:
  "socket_discharged (positive_meaning root_family_reading_system) root_family_socket_schema 1 False view_identity
    root_family_view"
  by (rule socket_discharged_carried[OF root_family_socket_carried])

corollary root_family_sibling_inputs:
  "pattern_variables (artifact_lookup_pattern data_x data_y (Pattern_Variable 4)) \<subseteq>
    socket_inputs view_identity root_family_view root_family_socket_schema 1"
  by (subst root_family_socket_inputs) auto

section \<open>The records, each at the system where its clauses stand\<close>

definition root_family_producer_record :: "(nat,nat,nat) resolution_declarations" where
  "root_family_producer_record = \<lparr>declared_producers = {|(79,root_family_view,[snd (snd root_family_view)])|},
    declared_consumers = {||},
    declared_sockets = {|(79,root_family_socket_schema,1,False,view_identity,root_family_view)|}\<rparr>"

definition root_family_closure_record :: "(nat,nat,nat) resolution_declarations" where
  "root_family_closure_record = \<lparr>declared_producers = {||},
    declared_consumers = {|(79,77,view_identity,0)|}, declared_sockets = {||}\<rparr>"

definition root_family_bound_record :: "(nat,nat,nat) resolution_declarations" where
  "root_family_bound_record = \<lparr>declared_producers = {||},
    declared_consumers = {|(79,47,view_swap,0)|}, declared_sockets = {||}\<rparr>"

definition root_family_membership_record :: "(nat,nat,nat) resolution_declarations" where
  "root_family_membership_record = \<lparr>declared_producers = {||}, declared_consumers = {||},
    declared_sockets = {|(83,membership_socket_schema,1,True,root_family_view,view_identity)|}\<rparr>"

theorem root_family_producer_record_discharged:
  "declarations_discharged (positive_meaning root_family_reading_system) root_family_producer_record
    root_family_correspondences"
  using root_family_producer_discharged root_family_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def root_family_producer_record_def
    root_family_view_formed view_identity_formed root_family_correspondences_root)

theorem root_family_closure_record_discharged:
  "declarations_discharged (positive_meaning package_closure_admission_system) root_family_closure_record
    root_family_correspondences"
  using root_family_closure_consumer
  by (simp add: declarations_discharged_def declarations_formed_def root_family_closure_record_def
    view_identity_formed root_family_correspondences_def)

theorem root_family_bound_record_discharged:
  "declarations_discharged (positive_meaning data_subset_system) root_family_bound_record root_family_correspondences"
  using root_family_bound_consumer
  by (simp add: declarations_discharged_def declarations_formed_def root_family_bound_record_def
    view_swap_formed root_family_correspondences_def)

theorem root_family_membership_record_discharged:
  "declarations_discharged (positive_meaning package_membership_system) root_family_membership_record
    root_family_correspondences"
  using membership_socket_discharged
  by (simp add: declarations_discharged_def declarations_formed_def root_family_membership_record_def
    view_identity_formed root_family_view_formed)

end
