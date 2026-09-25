theory Factor_Least_Witness_Facts
  imports Factor_Package_Additions Factor_Package_Requests
begin

section \<open>The answers the least witnesses are collected from\<close>

text \<open>
  A least witness is collected from the answers of the given's own readers: the selection reader (5)
  selects an element of a data list, the edge reader (82) relates two definition sites of a presented
  environment. The answers are read at a meaning, any set of calls; the least closure bound at an
  environment value and a root list is the least set containing the roots selected and closed under the
  edges answered, HOL's image of the reflexive transitive closure.
\<close>

abbreviation selection_answers :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> factor_term set" where
  "selection_answers M y \<equiv> {d. \<exists>r. (5,Pair_Term d (Pair_Term y r))\<in>M}"

abbreviation edge_answers :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> (factor_term\<times>factor_term) set" where
  "edge_answers M x \<equiv> {(d,e). (82,Pair_Term x (Pair_Term d e))\<in>M}"

abbreviation least_closure_bound :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term set" where
  "least_closure_bound M x y \<equiv> (edge_answers M x)\<^sup>* `` selection_answers M y"

lemma selection_answers_lists:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and member: "d\<in>selection_answers (positive_meaning P) y"
  shows "\<exists>xs. y=data_list_term xs \<and> data_elements xs \<and> d\<in>set xs"
proof -
  have "selected_data_member d y" using member selection by blast
  then show ?thesis by (simp only: selected_data_member_exact)
qed

lemma selection_answers_member:
  assumes selection: "\<And>t. (5::nat,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and data: "data_elements xs"
  shows "(\<exists>r. (5,Pair_Term d (Pair_Term (data_list_term xs) r))\<in>positive_meaning P) \<longleftrightarrow> d\<in>set xs"
  by (simp only: selection selected_data_member_exact data_list_term_injective) (use data in blast)

lemma selection_answers_exact:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and data: "data_elements xs"
  shows "selection_answers (positive_meaning P) (data_list_term xs)=set xs"
  using selection_answers_member[OF selection data] by blast

lemma selection_answers_finite:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
  shows "finite (selection_answers (positive_meaning P) y)"
proof (cases "\<exists>xs. y=data_list_term xs \<and> data_elements xs")
  case True
  then obtain xs where list: "y=data_list_term xs" "data_elements xs" by blast
  show ?thesis by (simp only: list(1) selection_answers_exact[OF selection list(2)]) simp
next
  case False
  then have "selection_answers (positive_meaning P) y={}" using selection_answers_lists[OF selection] by blast
  then show ?thesis by simp
qed

lemma edge_answers_exact:
  assumes edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and source: "environment_value_presents E x"
  shows "edge_answers (positive_meaning P) x=
    map_prod (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) ` native_definition_edges E"
proof (intro set_eqI)
  fix z :: "factor_term\<times>factor_term"
  obtain a b where shape: "z=(a,b)" by (cases z)
  have "z\<in>edge_answers (positive_meaning P) x \<longleftrightarrow>
      (\<exists>d f. a=definition_site_value d \<and> b=definition_site_value f \<and> (d,f)\<in>native_definition_edges E)"
    by (simp add: shape edges definition_edge_reading_at_source[OF source])
  also have "\<dots> \<longleftrightarrow>
      z\<in>map_prod (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) ` native_definition_edges E"
  proof
    assume "\<exists>d f. a=definition_site_value d \<and> b=definition_site_value f \<and> (d,f)\<in>native_definition_edges E"
    then obtain d f where parts: "a=definition_site_value d" "b=definition_site_value f"
      "(d,f)\<in>native_definition_edges E" by blast
    show "z\<in>map_prod (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) ` native_definition_edges E"
      unfolding shape parts(1,2) by (rule image_eqI[OF _ parts(3)]) simp
  next
    assume "z\<in>map_prod (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) ` native_definition_edges E"
    then obtain d f where edge: "z=(definition_site_value d,definition_site_value f)"
      "(d,f)\<in>native_definition_edges E" by auto
    show "\<exists>d f. a=definition_site_value d \<and> b=definition_site_value f \<and> (d,f)\<in>native_definition_edges E"
      using edge shape by blast
  qed
  finally show "z\<in>edge_answers (positive_meaning P) x \<longleftrightarrow>
      z\<in>map_prod (\<lambda>d. definition_site_value d) (\<lambda>d. definition_site_value d) ` native_definition_edges E" .
qed

lemma edge_answers_absent:
  assumes edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and absent: "\<not>(\<exists>E. environment_value_presents E x)"
  shows "edge_answers (positive_meaning P) x={}"
proof -
  have "(d,e)\<notin>edge_answers (positive_meaning P) x" for d e
  proof
    assume "(d,e)\<in>edge_answers (positive_meaning P) x"
    then have "(82,Pair_Term x (Pair_Term d e))\<in>positive_meaning definition_edge_reading_system"
      by (simp add: edges)
    then have "\<exists>F. environment_value_presents F x"
      by (simp only: definition_edge_reading_exact factor_term.inject) blast
    then show False using absent by blast
  qed
  then show ?thesis by blast
qed


lemma rtrancl_injective_image_set:
  assumes injective: "inj f"
  shows "(map_prod f f ` R)\<^sup>* `` (f ` S)=f ` (R\<^sup>* `` S)"
proof
  show "f ` (R\<^sup>* `` S)\<subseteq>(map_prod f f ` R)\<^sup>* `` (f ` S)"
  proof
    fix b assume "b\<in>f ` (R\<^sup>* `` S)"
    then obtain s t where parts: "s\<in>S" "(s,t)\<in>R\<^sup>*" "b=f t" by blast
    then show "b\<in>(map_prod f f ` R)\<^sup>* `` (f ` S)"
      using rtrancl_injective_image[OF injective, where x=s and y=t and R=R] by blast
  qed
  show "(map_prod f f ` R)\<^sup>* `` (f ` S)\<subseteq>f ` (R\<^sup>* `` S)"
  proof
    fix b assume "b\<in>(map_prod f f ` R)\<^sup>* `` (f ` S)"
    then obtain s where root: "s\<in>S" and path: "(f s,b)\<in>(map_prod f f ` R)\<^sup>*" by blast
    have "b\<in>range f"
    proof (cases "f s=b")
      case True
      then show ?thesis by blast
    next
      case False
      then obtain c where step: "(c,b)\<in>map_prod f f ` R" using path by (blast elim: rtranclE)
      obtain q where q: "(c,b)=map_prod f f q" "q\<in>R" by (rule imageE[OF step])
      show ?thesis using q(1) by (cases q) auto
    qed
    then obtain t where b: "b=f t" by blast
    have "(s,t)\<in>R\<^sup>*" using path by (simp only: b rtrancl_injective_image[OF injective])
    then show "b\<in>f ` (R\<^sup>* `` S)" using root b by blast
  qed
qed

section \<open>77's clause: a closed bound contains the least, and the least is the reach\<close>

theorem least_closure_bound_finite:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
  shows "finite (least_closure_bound (positive_meaning P) x y)"
proof -
  have answers: "finite (edge_answers (positive_meaning P) x)"
  proof (cases "\<exists>E. environment_value_presents E x")
    case True
    then obtain E where source: "environment_value_presents E x" by blast
    have "finite (native_definition_edges E)"
      using native_definition_edges_finite environment_value_presents_formed[OF source] by blast
    then show ?thesis by (simp only: edge_answers_exact[OF edges source]) (rule finite_imageI)
  next
    case False
    show ?thesis by (simp only: edge_answers_absent[OF edges False]) simp
  qed
  show ?thesis by (rule finite_rtrancl_Image[OF answers selection_answers_finite[OF selection]])
qed

theorem least_closure_bound_reach:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and source: "environment_value_presents E x"
    and data: "data_elements (map (\<lambda>d. definition_site_value d) rs)"
  shows "least_closure_bound (positive_meaning P) x (data_list_term (map (\<lambda>d. definition_site_value d) rs))=
    (\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)"
proof -
  have sites: "native_definition_sites E (set rs)=(native_definition_edges E)\<^sup>* `` set rs"
    by (auto simp: native_definition_sites_def)
  show ?thesis
    by (simp only: selection_answers_exact[OF selection data] edge_answers_exact[OF edges source] sites set_map
      rtrancl_injective_image_set[OF definition_site_value_injective])
qed

lemma closed_bound_contains_reach:
  assumes source: "environment_value_presents E x"
    and roots: "(47,Pair_Term y z)\<in>positive_meaning data_subset_system"
    and bound: "(76,Pair_Term (Pair_Term x z) z)\<in>positive_meaning definition_callee_list_system"
  obtains rs ys where "y=data_list_term (map (\<lambda>d. definition_site_value d) rs)" "z=data_list_term ys"
    "data_elements (map (\<lambda>d. definition_site_value d) rs)" "data_elements ys"
    "native_package_formed E (set rs)"
    "(\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)\<subseteq>set ys"
proof -
  obtain xs ys where bounds: "y=data_list_term xs" "z=data_list_term ys"
    "data_elements xs" "data_elements ys" "set xs\<subseteq>set ys"
    using roots by (auto simp: data_subset_exact)
  let ?P="\<lambda>d. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
  have entries: "\<forall>x\<in>set ys. \<exists>u r p C. x=site_data_term u r \<and> native_definition_at E u r p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys)"
    using bound by (simp only: bounds(2) definition_callee_list_on_values[OF source bounds(4)])
  have checked: "\<forall>x\<in>set ys. \<exists>d. x=definition_site_value d \<and> ?P d"
  proof (intro ballI)
    fix x assume member: "x\<in>set ys"
    obtain u r p C where parts: "x=site_data_term u r" "native_definition_at E u r p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
      using entries member by blast
    show "\<exists>d. x=definition_site_value d \<and> ?P d" by (rule exI[of _ "(u,r)"]) (use parts in auto)
  qed
  obtain ds where definitions: "ys=map (\<lambda>d. definition_site_value d) ds" "\<forall>d\<in>set ds. ?P d"
    using iffD1[OF list_range_restricted_witnesses checked] by blast
  have roots_listed: "\<forall>x\<in>set xs. \<exists>d. x=definition_site_value d \<and> d\<in>set ds"
    using bounds(5) definitions(1) by auto
  obtain rs where root_sites: "xs=map (\<lambda>d. definition_site_value d) rs" "set rs\<subseteq>set ds"
    using iffD1[OF list_range_restricted_witnesses roots_listed] by blast
  have defined: "\<forall>d\<in>set ds. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
    (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>set ds)"
    using definitions(2) by (simp add: definitions(1))
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  have package: "native_package_formed E (set rs)"
    by (simp only: native_package_finite_closed_bound)
      (use ef root_sites(2) defined in \<open>auto intro!: exI[of _ "set ds"]\<close>)
  have reached: "native_definition_sites E (set rs)\<subseteq>set ds"
    by (rule native_closed_bound_contains_sites[OF root_sites(2) defined])
  have listed: "y=data_list_term (map (\<lambda>d. definition_site_value d) rs)" using bounds(1) root_sites(1) by simp
  have data: "data_elements (map (\<lambda>d. definition_site_value d) rs)" using bounds(3) root_sites(1) by simp
  have contained: "(\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)\<subseteq>set ys"
    using reached definitions(1) by auto
  show ?thesis by (rule that[OF listed bounds(2) data bounds(4) package contained])
qed

lemma reach_bound_passes:
  assumes source: "environment_value_presents E x"
    and data: "data_elements (map (\<lambda>d. definition_site_value d) rs)"
    and package: "native_package_formed E (set rs)"
    and rows: "set zs=(\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)"
  shows "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) rs)) (data_list_term zs))
      \<in>positive_meaning data_subset_system"
    and "(76,Pair_Term (Pair_Term x (data_list_term zs)) (data_list_term zs))
      \<in>positive_meaning definition_callee_list_system"
proof -
  let ?U="native_definition_sites E (set rs)"
  have defined: "\<forall>d\<in>?U. \<exists>p C. native_definition_at E (fst d) (snd d) p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U)"
    by (rule native_package_sites_closed_bound[OF package])
  have formed: "term_formed (definition_site_value d)" if "d\<in>?U" for d
    using defined that native_definition_site_data_formed by blast
  have elements: "data_elements zs" using formed rows by auto
  have inside: "set (map (\<lambda>d. definition_site_value d) rs)\<subseteq>set zs"
    using rows native_definition_roots[of "set rs" E] by auto
  show "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) rs)) (data_list_term zs))
      \<in>positive_meaning data_subset_system"
    by (simp only: data_subset_lists) (use data elements inside in blast)
  show "(76,Pair_Term (Pair_Term x (data_list_term zs)) (data_list_term zs))
      \<in>positive_meaning definition_callee_list_system"
  proof (simp only: definition_callee_list_on_values[OF source elements], intro ballI)
    fix z assume "z\<in>set zs"
    then obtain d where d: "z=definition_site_value d" "d\<in>?U" using rows by auto
    obtain p C where own: "native_definition_at E (fst d) (snd d) p C"
      "\<forall>c S. (c,S)\<in>C \<longrightarrow> schema_dependencies S\<subseteq>?U" using defined d(2) by blast
    have image: "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set zs" if "(c,S)\<in>C" for c S
      using own(2) that rows by auto
    show "\<exists>u r p C. z=site_data_term u r \<and> native_definition_at E u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set zs)"
      using d(1) own(1) image by blast
  qed
qed

theorem closure_bound_least_witness:
  assumes environment: "\<And>t. (26,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
    and subset: "\<And>t. (47,t)\<in>positive_meaning P \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning P \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    and selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and rows: "set zs=least_closure_bound (positive_meaning P) x y"
  shows "(\<exists>z. (26,x)\<in>positive_meaning P \<and> (47,Pair_Term y z)\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term x z) z)\<in>positive_meaning P) \<longleftrightarrow>
    (26,x)\<in>positive_meaning P \<and> (47,Pair_Term y (data_list_term zs))\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term x (data_list_term zs)) (data_list_term zs))\<in>positive_meaning P"
proof
  assume "\<exists>z. (26,x)\<in>positive_meaning P \<and> (47,Pair_Term y z)\<in>positive_meaning P \<and>
    (76,Pair_Term (Pair_Term x z) z)\<in>positive_meaning P"
  then obtain z where held: "(26,x)\<in>positive_meaning P" "(47,Pair_Term y z)\<in>positive_meaning P"
    "(76,Pair_Term (Pair_Term x z) z)\<in>positive_meaning P" by blast
  obtain E where source: "environment_value_presents E x" using held(1) environment by blast
  obtain rs ys where parts: "y=data_list_term (map (\<lambda>d. definition_site_value d) rs)" "z=data_list_term ys"
    "data_elements (map (\<lambda>d. definition_site_value d) rs)" "data_elements ys"
    "native_package_formed E (set rs)"
    "(\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)\<subseteq>set ys"
    by (rule closed_bound_contains_reach[OF source iffD1[OF subset held(2)] iffD1[OF bound held(3)]])
  have reach: "set zs=(\<lambda>d. definition_site_value d) ` native_definition_sites E (set rs)"
    using rows unfolding parts(1) least_closure_bound_reach[OF selection edges source parts(3)] .
  show "(26,x)\<in>positive_meaning P \<and> (47,Pair_Term y (data_list_term zs))\<in>positive_meaning P \<and>
    (76,Pair_Term (Pair_Term x (data_list_term zs)) (data_list_term zs))\<in>positive_meaning P"
    using held(1) reach_bound_passes[OF source parts(3,5) reach] parts(1) by (simp add: subset bound)
next
  assume "(26,x)\<in>positive_meaning P \<and> (47,Pair_Term y (data_list_term zs))\<in>positive_meaning P \<and>
    (76,Pair_Term (Pair_Term x (data_list_term zs)) (data_list_term zs))\<in>positive_meaning P"
  then show "\<exists>z. (26,x)\<in>positive_meaning P \<and> (47,Pair_Term y z)\<in>positive_meaning P \<and>
    (76,Pair_Term (Pair_Term x z) z)\<in>positive_meaning P" by blast
qed

theorem package_closure_least_witness:
  assumes environment: "\<And>t. (26,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
    and subset: "\<And>t. (47,t)\<in>positive_meaning P \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning P \<longleftrightarrow> (76,t)\<in>positive_meaning definition_callee_list_system"
    and selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and rows: "set zs=least_closure_bound (positive_meaning P) (h 0) (h 1)"
  shows "(\<exists>a. term_formed a \<and> (\<forall>s d p. (s,d,p)\<in>schema_premises package_closure_admission_schema \<longrightarrow>
      (d,evaluate_pattern (h(2:=a)) p)\<in>positive_meaning P)) \<longleftrightarrow>
    (\<forall>s d p. (s,d,p)\<in>schema_premises package_closure_admission_schema \<longrightarrow>
      (d,evaluate_pattern (h(2:=data_list_term zs)) p)\<in>positive_meaning P)"
proof -
  have checked: "(\<forall>s d p. (s,d,p)\<in>schema_premises package_closure_admission_schema \<longrightarrow>
      (d,evaluate_pattern (h(2:=a)) p)\<in>positive_meaning P) \<longleftrightarrow>
    (26,h 0)\<in>positive_meaning P \<and> (47,Pair_Term (h 1) a)\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term (h 0) a) a)\<in>positive_meaning P" for a
    by (simp add: package_closure_admission_schema_def all_conj_distrib)
  have formed: "term_formed a" if "(47,Pair_Term (h 1) a)\<in>positive_meaning P" for a
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show ?thesis
    by (simp only: checked)
      (use closure_bound_least_witness[OF environment subset bound selection edges rows] formed in blast)
qed

section \<open>The additions notion's clause: the member check is antimonotone in the bound\<close>

context context_list_rule_relation
begin

lemma elements_antimono:
  assumes holds: "(list,Pair_Term a (data_list_term xs))\<in>M" and inside: "set ys\<subseteq>set xs"
  shows "(list,Pair_Term a (data_list_term ys))\<in>M"
proof -
  have parts: "term_formed a" "\<forall>x\<in>set xs. (element,Pair_Term a x)\<in>M"
    using holds by (auto simp: exact data_list_term_injective)
  show ?thesis by (simp only: exact) (use parts inside in blast)
qed

end

context package_additions_profile
begin

theorem bound_least_witness:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and source: "environment_value_presents F y"
    and rows: "set bs=least_closure_bound (positive_meaning P) y r"
  shows "(\<exists>b. (47,Pair_Term r b)\<in>positive_meaning P \<and> (76,Pair_Term (Pair_Term y b) b)\<in>positive_meaning P \<and>
      (list_site,Pair_Term c b)\<in>positive_meaning P) \<longleftrightarrow>
    (47,Pair_Term r (data_list_term bs))\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term y (data_list_term bs)) (data_list_term bs))\<in>positive_meaning P \<and>
      (list_site,Pair_Term c (data_list_term bs))\<in>positive_meaning P"
proof
  assume "\<exists>b. (47,Pair_Term r b)\<in>positive_meaning P \<and> (76,Pair_Term (Pair_Term y b) b)\<in>positive_meaning P \<and>
    (list_site,Pair_Term c b)\<in>positive_meaning P"
  then obtain b where held: "(47,Pair_Term r b)\<in>positive_meaning P"
    "(76,Pair_Term (Pair_Term y b) b)\<in>positive_meaning P" "(list_site,Pair_Term c b)\<in>positive_meaning P" by blast
  obtain rs ys where parts: "r=data_list_term (map (\<lambda>d. definition_site_value d) rs)" "b=data_list_term ys"
    "data_elements (map (\<lambda>d. definition_site_value d) rs)" "data_elements ys"
    "native_package_formed F (set rs)"
    "(\<lambda>d. definition_site_value d) ` native_definition_sites F (set rs)\<subseteq>set ys"
    by (rule closed_bound_contains_reach[OF source iffD1[OF subset_meaning held(1)] iffD1[OF bound_meaning held(2)]])
  have reach: "set bs=(\<lambda>d. definition_site_value d) ` native_definition_sites F (set rs)"
    using rows unfolding parts(1) least_closure_bound_reach[OF selection edges source parts(3)] .
  have listed: "(list_site,Pair_Term c (data_list_term bs))\<in>positive_meaning P"
    by (rule listing.semantics.elements_antimono[OF held(3)[unfolded parts(2)]]) (use reach parts(6) in blast)
  show "(47,Pair_Term r (data_list_term bs))\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term y (data_list_term bs)) (data_list_term bs))\<in>positive_meaning P \<and>
      (list_site,Pair_Term c (data_list_term bs))\<in>positive_meaning P"
    using reach_bound_passes[OF source parts(3,5) reach] parts(1) listed by (simp add: subset_meaning bound_meaning)
next
  assume "(47,Pair_Term r (data_list_term bs))\<in>positive_meaning P \<and>
      (76,Pair_Term (Pair_Term y (data_list_term bs)) (data_list_term bs))\<in>positive_meaning P \<and>
      (list_site,Pair_Term c (data_list_term bs))\<in>positive_meaning P"
  then show "\<exists>b. (47,Pair_Term r b)\<in>positive_meaning P \<and> (76,Pair_Term (Pair_Term y b) b)\<in>positive_meaning P \<and>
    (list_site,Pair_Term c b)\<in>positive_meaning P" by blast
qed

theorem entry_least_witness:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and rows: "set bs=least_closure_bound (positive_meaning P) (h 1) (h 4)"
  shows "(\<exists>a. term_formed a \<and> (\<forall>s d p. (s,d,p)\<in>schema_premises (package_additions_schema list_site) \<longrightarrow>
      (d,evaluate_pattern (h(5:=a)) p)\<in>positive_meaning P)) \<longleftrightarrow>
    (\<forall>s d p. (s,d,p)\<in>schema_premises (package_additions_schema list_site) \<longrightarrow>
      (d,evaluate_pattern (h(5:=data_list_term bs)) p)\<in>positive_meaning P)"
proof -
  let ?c="Pair_Term (h 0) (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
  have checked: "(\<forall>s d p. (s,d,p)\<in>schema_premises (package_additions_schema list_site) \<longrightarrow>
      (d,evaluate_pattern (h(5:=a)) p)\<in>positive_meaning P) \<longleftrightarrow>
    ((156,h 0)\<in>positive_meaning P \<and> (156,Pair_Term (h 1) (Pair_Term (h 2) (h 3)))\<in>positive_meaning P \<and>
      (79,Pair_Term (Pair_Term (h 1) (h 2)) (Pair_Term (h 3) (h 4)))\<in>positive_meaning P) \<and>
    ((47,Pair_Term (h 4) a)\<in>positive_meaning P \<and> (76,Pair_Term (Pair_Term (h 1) a) a)\<in>positive_meaning P \<and>
      (list_site,Pair_Term ?c a)\<in>positive_meaning P)" for a
    by (simp add: package_additions_schema_def all_conj_distrib)
  have formed: "term_formed a" if "(47,Pair_Term (h 4) a)\<in>positive_meaning P" for a
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show ?thesis
  proof (cases "(156,Pair_Term (h 1) (Pair_Term (h 2) (h 3)))\<in>positive_meaning P")
    case True
    then obtain F v s where "site_value_presents F v s (Pair_Term (h 1) (Pair_Term (h 2) (h 3)))"
      by (auto simp: site_meaning)
    then have source: "environment_value_presents F (h 1)"
      by (auto simp: site_value_presents_def site_data_term_def)
    show ?thesis
      by (simp only: checked) (use bound_least_witness[OF selection edges source rows, of ?c] formed in blast)
  next
    case False
    then show ?thesis by (simp only: checked) simp
  qed
qed

end

section \<open>561's clause: a formed environment including both exists exactly when the two are compatible\<close>

text \<open>
  The rows of an environment value are the answers of the selection reader over its two tables, the value
  matched as the pair of its artifact table and its binding table. An answer's key is its first component
  (an artifact row's use, a binding row's use and slot); two artifact answers of one key are identified
  when artifact identity (12) holds at their artifact values, two binding answers when their targets are
  equal. A conflict is two answers of one key that are not identified.
\<close>

abbreviation artifact_row_answers :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> factor_term set" where
  "artifact_row_answers M x \<equiv> {d. \<exists>a b. x=Pair_Term a b \<and> d\<in>selection_answers M a}"

abbreviation binding_row_answers :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> factor_term set" where
  "binding_row_answers M x \<equiv> {d. \<exists>a b. x=Pair_Term a b \<and> d\<in>selection_answers M b}"

fun answer_key :: "factor_term \<Rightarrow> factor_term" where
  "answer_key (Pair_Term k a)=k"
| "answer_key t=t"

definition row_answers_conflict :: "(nat\<times>factor_term) set \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "row_answers_conflict M x v \<longleftrightarrow>
    (\<exists>k a b. Pair_Term k a\<in>artifact_row_answers M x \<union> artifact_row_answers M v \<and>
      Pair_Term k b\<in>artifact_row_answers M x \<union> artifact_row_answers M v \<and> (12,Pair_Term a b)\<notin>M) \<or>
    (\<exists>k a b. Pair_Term k a\<in>binding_row_answers M x \<union> binding_row_answers M v \<and>
      Pair_Term k b\<in>binding_row_answers M x \<union> binding_row_answers M v \<and> a\<noteq>b)"


lemma environment_value_answers:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and source: "environment_value_presents E x"
  shows "\<forall>t\<in>artifact_row_answers (positive_meaning P) x.
      \<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z t"
    and "\<forall>z\<in>environment_artifacts E.
      \<exists>t\<in>artifact_row_answers (positive_meaning P) x. environment_artifact_entry_presents z t"
    and "binding_row_answers (positive_meaning P) x=binding_data ` environment_bindings E"
proof -
  have ef: "environment_formed E" using environment_value_presents_formed[OF source] by blast
  obtain a b where parts: "data_collection_presents environment_artifact_entry_presents (environment_artifacts E) a"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings E) b" "x=Pair_Term a b"
    using source unfolding environment_value_presents_def by blast
  have artifacts: "(\<forall>z\<in>environment_artifacts E. \<exists>t. selected_data_member t a \<and>
        environment_artifact_entry_presents z t) \<and>
      (\<forall>t. selected_data_member t a \<longrightarrow> (\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z t))"
    by (rule data_collection_selection[OF parts(1)]) (use environment_artifact_entry_formed in blast)
  have bindings: "(\<forall>z\<in>environment_bindings E. \<exists>t. selected_data_member t b \<and> t=binding_data z) \<and>
      (\<forall>t. selected_data_member t b \<longrightarrow> (\<exists>z\<in>environment_bindings E. t=binding_data z))"
    by (rule data_collection_selection[OF parts(2)]) (use binding_data_formed[OF ef] in auto)
  have artifact_answer: "t\<in>artifact_row_answers (positive_meaning P) x \<longleftrightarrow> selected_data_member t a" for t
    by (simp add: parts(3) selection)
  have binding_answer: "t\<in>binding_row_answers (positive_meaning P) x \<longleftrightarrow> selected_data_member t b" for t
    by (simp add: parts(3) selection)
  show "\<forall>t\<in>artifact_row_answers (positive_meaning P) x.
      \<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z t"
  proof
    fix t assume "t\<in>artifact_row_answers (positive_meaning P) x"
    then have "selected_data_member t a" by (simp only: artifact_answer)
    then show "\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z t" using artifacts by blast
  qed
  show "\<forall>z\<in>environment_artifacts E.
      \<exists>t\<in>artifact_row_answers (positive_meaning P) x. environment_artifact_entry_presents z t"
  proof
    fix z assume "z\<in>environment_artifacts E"
    then obtain t where t: "selected_data_member t a" "environment_artifact_entry_presents z t"
      using artifacts by blast
    have member: "t\<in>artifact_row_answers (positive_meaning P) x" using t(1) by (simp only: artifact_answer)
    show "\<exists>t\<in>artifact_row_answers (positive_meaning P) x. environment_artifact_entry_presents z t"
      by (rule bexI[where x=t and P="environment_artifact_entry_presents z", OF t(2) member])
  qed
  show "binding_row_answers (positive_meaning P) x=binding_data ` environment_bindings E"
  proof (intro set_eqI iffI)
    fix t assume "t\<in>binding_row_answers (positive_meaning P) x"
    then have "selected_data_member t b" by (simp only: binding_answer)
    then show "t\<in>binding_data ` environment_bindings E" using bindings by blast
  next
    fix t assume "t\<in>binding_data ` environment_bindings E"
    then have "selected_data_member t b" using bindings by blast
    then show "t\<in>binding_row_answers (positive_meaning P) x" by (simp only: binding_answer)
  qed
qed

lemma artifact_answers_conflict:
  assumes identity: "\<And>t. (12,t)\<in>positive_meaning P \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    and forward: "\<forall>t\<in>A. \<exists>z\<in>Z. environment_artifact_entry_presents z t"
    and backward: "\<forall>z\<in>Z. \<exists>t\<in>A. environment_artifact_entry_presents z t"
  shows "(\<exists>k a b. Pair_Term k a\<in>A \<and> Pair_Term k b\<in>A \<and> (12,Pair_Term a b)\<notin>positive_meaning P) \<longleftrightarrow>
    (\<exists>u R S. (u,R)\<in>Z \<and> (u,S)\<in>Z \<and> R\<noteq>S)"
proof
  assume "\<exists>k a b. Pair_Term k a\<in>A \<and> Pair_Term k b\<in>A \<and> (12,Pair_Term a b)\<notin>positive_meaning P"
  then obtain k a b where rows: "Pair_Term k a\<in>A" "Pair_Term k b\<in>A" "(12,Pair_Term a b)\<notin>positive_meaning P"
    by blast
  obtain z where z: "z\<in>Z" "environment_artifact_entry_presents z (Pair_Term k a)" using forward rows(1) by blast
  obtain y where y: "y\<in>Z" "environment_artifact_entry_presents y (Pair_Term k b)" using forward rows(2) by blast
  have parts: "k=use_data_term (fst z)" "artifact_value_presents (snd z) a"
    "k=use_data_term (fst y)" "artifact_value_presents (snd y) b"
    using z(2) y(2) by (auto simp: environment_artifact_entry_presents_def)
  have same: "fst z=fst y" using parts(1,3) injD[OF use_data_term_injective] by metis
  have different: "snd z\<noteq>snd y"
    using rows(3) by (simp add: identity admitted_artifact_comparison[OF parts(2,4)])
  show "\<exists>u R S. (u,R)\<in>Z \<and> (u,S)\<in>Z \<and> R\<noteq>S"
    using z(1) y(1) same different by (metis prod.collapse)
next
  assume "\<exists>u R S. (u,R)\<in>Z \<and> (u,S)\<in>Z \<and> R\<noteq>S"
  then obtain u R S where rows: "(u,R)\<in>Z" "(u,S)\<in>Z" "R\<noteq>S" by blast
  obtain t where t: "t\<in>A" "environment_artifact_entry_presents (u,R) t" using backward rows(1) by blast
  obtain w where w: "w\<in>A" "environment_artifact_entry_presents (u,S) w" using backward rows(2) by blast
  obtain a b where parts: "t=Pair_Term (use_data_term u) a" "artifact_value_presents R a"
    "w=Pair_Term (use_data_term u) b" "artifact_value_presents S b"
    using t(2) w(2) by (auto simp: environment_artifact_entry_presents_def)
  have refuted: "(12,Pair_Term a b)\<notin>positive_meaning P"
    using rows(3) by (simp add: identity admitted_artifact_comparison[OF parts(2,4)])
  show "\<exists>k a b. Pair_Term k a\<in>A \<and> Pair_Term k b\<in>A \<and> (12,Pair_Term a b)\<notin>positive_meaning P"
    using t(1) w(1) parts(1,3) refuted by blast
qed

lemma binding_answers_conflict:
  "(\<exists>k a b. Pair_Term k a\<in>binding_data ` B \<and> Pair_Term k b\<in>binding_data ` B \<and> a\<noteq>b) \<longleftrightarrow>
    (\<exists>u s w w'. ((u,s),w)\<in>B \<and> ((u,s),w')\<in>B \<and> w\<noteq>w')"
proof
  assume "\<exists>k a b. Pair_Term k a\<in>binding_data ` B \<and> Pair_Term k b\<in>binding_data ` B \<and> a\<noteq>b"
  then obtain k a b z y where rows: "z\<in>B" "Pair_Term k a=binding_data z" "y\<in>B" "Pair_Term k b=binding_data y" "a\<noteq>b"
    by blast
  obtain u s w where z: "z=((u,s),w)" by (metis prod.collapse)
  obtain u' s' w' where y: "y=((u',s'),w')" by (metis prod.collapse)
  have same: "u'=u" "s'=s" "w\<noteq>w'"
    using rows(2,4,5) by (auto simp: z y binding_data_def inj_eq[OF use_data_term_injective])
  show "\<exists>u s w w'. ((u,s),w)\<in>B \<and> ((u,s),w')\<in>B \<and> w\<noteq>w'" using rows(1,3) z y same by blast
next
  assume "\<exists>u s w w'. ((u,s),w)\<in>B \<and> ((u,s),w')\<in>B \<and> w\<noteq>w'"
  then obtain u s w w' where rows: "((u,s),w)\<in>B" "((u,s),w')\<in>B" "w\<noteq>w'" by blast
  have first: "Pair_Term (Pair_Term (use_data_term u) (Payload_Term s)) (use_data_term w)\<in>binding_data ` B"
    by (rule image_eqI[OF _ rows(1)]) (simp add: binding_data_def)
  have second: "Pair_Term (Pair_Term (use_data_term u) (Payload_Term s)) (use_data_term w')\<in>binding_data ` B"
    by (rule image_eqI[OF _ rows(2)]) (simp add: binding_data_def)
  have different: "use_data_term w\<noteq>use_data_term w'" using rows(3) by (simp add: inj_eq[OF use_data_term_injective])
  show "\<exists>k a b. Pair_Term k a\<in>binding_data ` B \<and> Pair_Term k b\<in>binding_data ` B \<and> a\<noteq>b"
    using first second different by blast
qed

theorem environment_row_conflict:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning P \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    and left: "environment_value_presents E x" and right: "environment_value_presents F v"
  shows "row_answers_conflict (positive_meaning P) x v \<longleftrightarrow> \<not>environments_compatible E F"
proof -
  have ef: "environment_formed E" "environment_formed F"
    using environment_value_presents_formed[OF left] environment_value_presents_formed[OF right] by blast+
  note lx=environment_value_answers[OF selection left] and lv=environment_value_answers[OF selection right]
  have artifacts: "(\<exists>k a b. Pair_Term k a\<in>artifact_row_answers (positive_meaning P) x \<union>
        artifact_row_answers (positive_meaning P) v \<and>
      Pair_Term k b\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v \<and>
      (12,Pair_Term a b)\<notin>positive_meaning P) \<longleftrightarrow>
    (\<exists>u R S. (u,R)\<in>environment_artifacts E \<union> environment_artifacts F \<and>
      (u,S)\<in>environment_artifacts E \<union> environment_artifacts F \<and> R\<noteq>S)"
  proof (rule artifact_answers_conflict[OF identity])
    show "\<forall>t\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v.
        \<exists>z\<in>environment_artifacts E \<union> environment_artifacts F. environment_artifact_entry_presents z t"
      unfolding ball_Un bex_Un using lx(1) lv(1) by blast
    show "\<forall>z\<in>environment_artifacts E \<union> environment_artifacts F.
        \<exists>t\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v.
          environment_artifact_entry_presents z t"
      unfolding ball_Un bex_Un using lx(2) lv(2) by blast
  qed
  have bindings: "(\<exists>k a b. Pair_Term k a\<in>binding_row_answers (positive_meaning P) x \<union>
        binding_row_answers (positive_meaning P) v \<and>
      Pair_Term k b\<in>binding_row_answers (positive_meaning P) x \<union> binding_row_answers (positive_meaning P) v \<and>
      a\<noteq>b) \<longleftrightarrow>
    (\<exists>u s w w'. ((u,s),w)\<in>environment_bindings E \<union> environment_bindings F \<and>
      ((u,s),w')\<in>environment_bindings E \<union> environment_bindings F \<and> w\<noteq>w')"
    unfolding lx(3) lv(3) image_Un[symmetric] by (rule binding_answers_conflict)
  have artifact_compatible: "(\<exists>u R S. (u,R)\<in>environment_artifacts E \<union> environment_artifacts F \<and>
      (u,S)\<in>environment_artifacts E \<union> environment_artifacts F \<and> R\<noteq>S) \<longleftrightarrow>
    \<not>(\<forall>u R S. artifact_at E u R \<longrightarrow> artifact_at F u S \<longrightarrow> R=S)"
    using environment_artifact_unique[OF ef(1)] environment_artifact_unique[OF ef(2)]
    unfolding artifact_at_def by blast
  have binding_compatible: "(\<exists>u s w w'. ((u,s),w)\<in>environment_bindings E \<union> environment_bindings F \<and>
      ((u,s),w')\<in>environment_bindings E \<union> environment_bindings F \<and> w\<noteq>w') \<longleftrightarrow>
    \<not>(\<forall>u k v w. binds_slot E u k v \<longrightarrow> binds_slot F u k w \<longrightarrow> v=w)"
    using environment_binding_unique[OF ef(1)] environment_binding_unique[OF ef(2)]
    unfolding binds_slot_def by blast
  show ?thesis
    unfolding row_answers_conflict_def environments_compatible_def artifacts bindings artifact_compatible
      binding_compatible by blast
qed

lemma union_rows:
  assumes "\<forall>t\<in>A. \<exists>z\<in>Z. Q z t" "\<forall>t\<in>B. \<exists>z\<in>W. Q z t"
  shows "\<forall>t\<in>A \<union> B. \<exists>z\<in>Z \<union> W. Q z t"
  using assms by blast


theorem merge_rows_presented:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning P \<longleftrightarrow> (12,t)\<in>positive_meaning artifact_identity_system"
    and left: "environment_value_presents E x" and right: "environment_value_presents F v"
    and free: "\<not>row_answers_conflict (positive_meaning P) x v"
    and artifact_rows: "set ts\<subseteq>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v"
      "distinct (map answer_key ts)"
      "\<forall>t\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v.
        \<exists>t'\<in>set ts. answer_key t'=answer_key t"
    and binding_rows: "set qs\<subseteq>binding_row_answers (positive_meaning P) x \<union> binding_row_answers (positive_meaning P) v"
      "distinct (map answer_key qs)"
      "\<forall>q\<in>binding_row_answers (positive_meaning P) x \<union> binding_row_answers (positive_meaning P) v.
        \<exists>q'\<in>set qs. answer_key q'=answer_key q"
  shows "environment_value_presents (merge_environment E F) (Pair_Term (data_list_term ts) (data_list_term qs))"
proof -
  let ?A="environment_artifacts E \<union> environment_artifacts F"
  let ?B="environment_bindings E \<union> environment_bindings F"
  have ef: "environment_formed E" "environment_formed F"
    using environment_value_presents_formed[OF left] environment_value_presents_formed[OF right] by blast+
  have compatible: "environments_compatible E F"
    using free environment_row_conflict[OF selection identity left right] by blast
  have merged: "environment_formed (merge_environment E F)"
    using environment_merge_formed_iff[OF ef] compatible by blast
  have functional: "single_valued ?A" "single_valued ?B"
    using merged by (simp_all add: environment_formed_def merge_environment_def)
  note lx=environment_value_answers[OF selection left] and lv=environment_value_answers[OF selection right]
  have rows_forward: "\<forall>t\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v.
      \<exists>z\<in>?A. environment_artifact_entry_presents z t"
    by (rule union_rows[OF lx(1) lv(1)])
  have forward: "\<forall>t\<in>set ts. \<exists>z. z\<in>?A \<and> environment_artifact_entry_presents z t"
  proof
    fix t assume member: "t\<in>set ts"
    have "\<exists>z\<in>?A. environment_artifact_entry_presents z t"
      by (rule bspec[OF rows_forward subsetD[OF artifact_rows(1) member]])
    then show "\<exists>z. z\<in>?A \<and> environment_artifact_entry_presents z t" by blast
  qed
  obtain zs where paired: "list_all2 (\<lambda>z t. z\<in>?A \<and> environment_artifact_entry_presents z t) zs ts"
    using list_all2_exists_left[where ys=ts and R="\<lambda>z t. z\<in>?A \<and> environment_artifact_entry_presents z t"] forward
    by blast
  have keys: "map (\<lambda>z. use_data_term (fst z)) zs=map answer_key ts"
    using paired by (induction rule: list_all2_induct) (auto simp: environment_artifact_entry_presents_def)
  have "distinct (map (\<lambda>z. use_data_term (fst z)) zs)" using artifact_rows(2) keys by simp
  then have distinct: "distinct zs" by (simp add: distinct_map)
  have inside: "set zs\<subseteq>?A" using list_all2_members[OF paired] by blast
  have covered: "?A\<subseteq>set zs"
  proof
    fix z assume member: "z\<in>?A"
    obtain t where t: "t\<in>artifact_row_answers (positive_meaning P) x \<union> artifact_row_answers (positive_meaning P) v"
      "environment_artifact_entry_presents z t" by (rule bexE[OF bspec[OF union_rows[OF lx(2) lv(2)] member]])
    obtain t' where t': "t'\<in>set ts" "answer_key t'=answer_key t"
      by (rule bexE[OF bspec[OF artifact_rows(3) t(1)]])
    obtain z' where z': "z'\<in>set zs" "z'\<in>?A" "environment_artifact_entry_presents z' t'"
      using list_all2_members[OF paired] t'(1) by blast
    have same_use: "fst z'=fst z"
      using t(2) z'(3) t'(2) by (auto simp: environment_artifact_entry_presents_def inj_eq[OF use_data_term_injective])
    have "z'=z" using functional(1) z'(2) member same_use unfolding single_valued_def by (metis prod.collapse)
    then show "z\<in>set zs" using z'(1) by simp
  qed
  have read: "list_all2 environment_artifact_entry_presents zs ts" using paired by (rule list_all2_mono) blast
  have artifacts: "data_collection_presents environment_artifact_entry_presents ?A (data_list_term ts)"
    unfolding data_collection_presents_def
    by (rule exI[of _ zs], rule exI[of _ ts]) (use distinct inside covered read in auto)
  have bforward: "\<forall>q\<in>set qs. \<exists>z. z\<in>?B \<and> q=binding_data z"
    using binding_rows(1) unfolding lx(3) lv(3) by blast
  obtain ws where bpaired: "list_all2 (\<lambda>z q. z\<in>?B \<and> q=binding_data z) ws qs"
    using list_all2_exists_left[where ys=qs and R="\<lambda>z q. z\<in>?B \<and> q=binding_data z"] bforward by blast
  have mapped: "qs=map binding_data ws" using bpaired by (induction rule: list_all2_induct) auto
  have binside: "set ws\<subseteq>?B" using list_all2_members[OF bpaired] by blast
  have "distinct (map (\<lambda>z. answer_key (binding_data z)) ws)" using binding_rows(2) mapped by (simp add: comp_def)
  then have bdistinct: "distinct ws" by (simp add: distinct_map)
  have bcovered: "?B\<subseteq>set ws"
  proof
    fix z assume member: "z\<in>?B"
    have answer: "binding_data z\<in>binding_row_answers (positive_meaning P) x \<union> binding_row_answers (positive_meaning P) v"
      using member unfolding lx(3) lv(3) by blast
    obtain q' where q': "q'\<in>set qs" "answer_key q'=answer_key (binding_data z)"
      by (rule bexE[OF bspec[OF binding_rows(3) answer]])
    obtain z' where z': "z'\<in>set ws" "q'=binding_data z'" using mapped q'(1) by auto
    have other: "z'\<in>?B" using binside z'(1) by blast
    have same: "fst z'=fst z"
      using q'(2) z'(2) by (cases z; cases z') (auto simp: binding_data_def prod_eq_iff inj_eq[OF use_data_term_injective])
    have "z'=z" using functional(2) other member same unfolding single_valued_def by (metis prod.collapse)
    then show "z\<in>set ws" using z'(1) by simp
  qed
  have bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) ?B (data_list_term qs)"
    unfolding data_collection_presents_def
    by (rule exI[of _ ws], rule exI[of _ qs]) (use bdistinct binside bcovered mapped in \<open>auto simp: list_all2_function\<close>)
  show ?thesis
    unfolding environment_value_presents_def
    using merged artifacts bindings by (auto simp: merge_environment_def)
qed

lemma included_compatible:
  assumes formed: "environment_formed G"
    and left: "environment_included E G" and right: "environment_included F G"
  shows "environments_compatible E F"
proof -
  have artifacts: "R=S" if "artifact_at E u R" "artifact_at F u S" for u R S
    using environment_artifact_unique[OF formed] that left right
    unfolding environment_included_def artifact_at_def by blast
  have bindings: "v=w" if "binds_slot E u k v" "binds_slot F u k w" for u k v w
    using environment_binding_unique[OF formed] that left right
    unfolding environment_included_def binds_slot_def by blast
  show ?thesis unfolding environments_compatible_def using artifacts bindings by blast
qed

lemma inclusion_at:
  assumes inclusion: "\<And>t. (113,t)\<in>positive_meaning P \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    and source: "environment_value_presents E e" and target: "environment_value_presents G f"
  shows "(113,Pair_Term e f)\<in>positive_meaning P \<longleftrightarrow> environment_included E G"
  by (simp only: inclusion environment_inclusion_on_values[OF source target])

lemma inclusion_sound:
  assumes inclusion: "\<And>t. (113,t)\<in>positive_meaning P \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    and held: "(113,Pair_Term e f)\<in>positive_meaning P"
  obtains E G where "environment_value_presents E e" "environment_value_presents G f" "environment_included E G"
  using held by (simp only: inclusion environment_inclusion_exact factor_term.inject) blast

theorem merge_least_witness:
  assumes inclusion: "\<And>t. (113,t)\<in>positive_meaning P \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
  shows "(\<exists>g. (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P) \<longleftrightarrow>
      (\<exists>E F. environment_value_presents E x \<and> environment_value_presents F v \<and> environments_compatible E F)"
    and "environment_value_presents E x \<Longrightarrow> environment_value_presents F v \<Longrightarrow>
      environment_value_presents (merge_environment E F) g \<Longrightarrow>
      (\<exists>g'. (113,Pair_Term x g')\<in>positive_meaning P \<and> (113,Pair_Term v g')\<in>positive_meaning P) \<longleftrightarrow>
      (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P"
proof -
  show "(\<exists>g. (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P) \<longleftrightarrow>
      (\<exists>E F. environment_value_presents E x \<and> environment_value_presents F v \<and> environments_compatible E F)"
  proof
    assume "\<exists>g. (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P"
    then obtain g where held: "(113,Pair_Term x g)\<in>positive_meaning P" "(113,Pair_Term v g)\<in>positive_meaning P"
      by blast
    obtain E G where l: "environment_value_presents E x" "environment_value_presents G g" "environment_included E G"
      by (rule inclusion_sound[OF inclusion held(1)])
    obtain F G' where r: "environment_value_presents F v" "environment_value_presents G' g"
      "environment_included F G'" by (rule inclusion_sound[OF inclusion held(2)])
    have same: "G'=G" by (rule environment_value_presents_unique[OF r(2) l(2)])
    have formed: "environment_formed G" using environment_value_presents_formed[OF l(2)] by blast
    have "environments_compatible E F" using included_compatible[OF formed l(3)] r(3) same by blast
    then show "\<exists>E F. environment_value_presents E x \<and> environment_value_presents F v \<and> environments_compatible E F"
      using l(1) r(1) by blast
  next
    assume "\<exists>E F. environment_value_presents E x \<and> environment_value_presents F v \<and> environments_compatible E F"
    then obtain E F where parts: "environment_value_presents E x" "environment_value_presents F v"
      "environments_compatible E F" by blast
    have ef: "environment_formed E" "environment_formed F"
      using environment_value_presents_formed[OF parts(1)] environment_value_presents_formed[OF parts(2)] by blast+
    have merged: "environment_formed (merge_environment E F)"
      using environment_merge_formed_iff[OF ef] parts(3) by blast
    obtain g where g: "environment_value_presents (merge_environment E F) g"
      using environment_value_presents_total[OF merged] by blast
    show "\<exists>g. (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P"
      using inclusion_at[OF inclusion parts(1) g] inclusion_at[OF inclusion parts(2) g]
        environment_included_merge_left[of E F] environment_included_merge_right[of F E] by blast
  qed
  show "(\<exists>g'. (113,Pair_Term x g')\<in>positive_meaning P \<and> (113,Pair_Term v g')\<in>positive_meaning P) \<longleftrightarrow>
      (113,Pair_Term x g)\<in>positive_meaning P \<and> (113,Pair_Term v g)\<in>positive_meaning P"
    if left: "environment_value_presents E x" and right: "environment_value_presents F v"
      and merged: "environment_value_presents (merge_environment E F) g"
  proof -
    have both: "(113,Pair_Term x g)\<in>positive_meaning P" "(113,Pair_Term v g)\<in>positive_meaning P"
      using inclusion_at[OF inclusion left merged] inclusion_at[OF inclusion right merged]
        environment_included_merge_left[of E F] environment_included_merge_right[of F E] by blast+
    then show ?thesis by blast
  qed
qed

theorem package_request_least_witness:
  assumes inclusion: "\<And>t. (113,t)\<in>positive_meaning P \<longleftrightarrow> (113,t)\<in>positive_meaning environment_inclusion_system"
    and left: "environment_value_presents E (h 0)" and right: "environment_value_presents F (h 4)"
    and merged: "environment_value_presents (merge_environment E F) g"
  shows "(\<exists>a. term_formed a \<and> (\<forall>s d p. (s,d,p)\<in>schema_premises package_request_schema \<longrightarrow>
      (d,evaluate_pattern (h(7:=a)) p)\<in>positive_meaning P)) \<longleftrightarrow>
    (\<forall>s d p. (s,d,p)\<in>schema_premises package_request_schema \<longrightarrow>
      (d,evaluate_pattern (h(7:=g)) p)\<in>positive_meaning P)"
proof -
  have checked: "(\<forall>s d p. (s,d,p)\<in>schema_premises package_request_schema \<longrightarrow>
      (d,evaluate_pattern (h(7:=a)) p)\<in>positive_meaning P) \<longleftrightarrow>
    ((80,Pair_Term (Pair_Term (h 0) (h 1)) (h 2))\<in>positive_meaning P \<and>
      (560,Pair_Term (Pair_Term (Pair_Term (h 0) (h 1)) (h 2)) (h 3))\<in>positive_meaning P \<and>
      (79,Pair_Term (Pair_Term (h 4) (h 5)) (Pair_Term (h 6) (h 3)))\<in>positive_meaning P \<and>
      (122,Pair_Term (h 4) (Pair_Term (h 5) (h 6)))\<in>positive_meaning P) \<and>
    ((113,Pair_Term (h 0) a)\<in>positive_meaning P \<and> (113,Pair_Term (h 4) a)\<in>positive_meaning P)" for a
    by (simp add: package_request_schema_def all_conj_distrib)
  have formed: "term_formed a" if "(113,Pair_Term (h 0) a)\<in>positive_meaning P" for a
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  have least: "(\<exists>a. (113,Pair_Term (h 0) a)\<in>positive_meaning P \<and> (113,Pair_Term (h 4) a)\<in>positive_meaning P) \<longleftrightarrow>
      (113,Pair_Term (h 0) g)\<in>positive_meaning P \<and> (113,Pair_Term (h 4) g)\<in>positive_meaning P"
    by (rule merge_least_witness(2)[OF inclusion left right merged])
  show ?thesis by (simp only: checked) (use least formed in blast)
qed

end
