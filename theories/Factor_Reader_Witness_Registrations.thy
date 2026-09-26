theory Factor_Reader_Witness_Registrations
  imports Factor_Least_Witness_Registrations Factor_Least_Witness_Facts
begin

section \<open>The given's registrations\<close>

text \<open>
  The four registrations of task 496's entry (its item 4), as data over the numbered given's readers: 77's bound
  and the additions notion's bound at any list site, each the reach of the roots over the definition edges, and
  561's private environment, the rows of the two environments. Each is complete at every program whose read sites
  have the numbered readers' meanings, stated as the equations @{text Factor_Least_Witness_Facts} takes, by those
  facts; W2's contract identifies each registration's collection with the least witness there. A registration is
  read by the construction alone: no clause is refined, restated or added, and the checker reads none. They stand
  above both the generic contract (@{text Factor_Least_Witness_Registrations}), which reads no package reader, and
  W3's facts, so a change of a reader rebuilds these registrations and not the contract.
\<close>

subsection \<open>The premises that bind a registered variable, and a presented schema's premises\<close>

lemma fimage_fst_binding:
  assumes "c |\<in>| fimage fst B"
  obtains t where "(c,t) |\<in>| B"
proof -
  obtain y where y: "c=fst y" "y |\<in>| B" using assms by (rule fimageE)
  show thesis by (rule that[of "snd y"]) (use y in simp)
qed

lemma finite_schema_of_premises_member:
  assumes "finite (schema_premises S)"
  shows "z |\<in>| finite_schema_premises (finite_schema_of S) \<longleftrightarrow>
    z \<in> (\<lambda>(k,v). (k,map_prod id finite_pattern_of v)) ` schema_premises S"
proof -
  have "fset (Abs_fset (map_relation_values (map_prod id finite_pattern_of) (schema_premises S)))=
      map_relation_values (map_prod id finite_pattern_of) (schema_premises S)"
    by (rule Abs_fset_inverse) (simp add: assms)
  then show ?thesis by (simp add: finite_schema_of_def map_relation_values_def)
qed

lemma finite_schema_of_materials_member:
  assumes "finite (schema_material_premises S)"
  shows "z |\<in>| finite_schema_materials (finite_schema_of S) \<longleftrightarrow>
    z \<in> (\<lambda>(k,v). (k,finite_material_of v)) ` schema_material_premises S"
proof -
  have "fset (Abs_fset (map_relation_values finite_material_of (schema_material_premises S)))=
      map_relation_values finite_material_of (schema_material_premises S)"
    by (rule Abs_fset_inverse) (simp add: assms)
  then show ?thesis by (simp add: finite_schema_of_def map_relation_values_def)
qed

subsection \<open>The selection and edge queries and their answers\<close>

text \<open>
  The selection query answers the elements the selection reader (5) selects from a list its equation matches; the
  edge query, at an element d, the definitions the edge reader (82) relates to d in an environment value. Their
  answers are exactly the reader's answers at the decoded bindings (@{text witness_selection_query_answers},
  @{text witness_edge_query_answers}): every true call of a reader is formed, so has a finite presentation.
\<close>

definition witness_selection_query :: "'a \<Rightarrow> nat finite_term_pattern \<Rightarrow> nat \<Rightarrow> ('a,nat,nat) collection_query" where
  "witness_selection_query c pe l=\<lparr>query_equations=[(c,pe)],query_site=5,
    query_goal=Finite_Pattern_Pair (Finite_Variable 3) (Finite_Pattern_Pair (Finite_Variable l) (Finite_Variable 4)),
    query_element=3\<rparr>"

definition witness_edge_query :: "'a \<Rightarrow> ('a,nat,nat) collection_query" where
  "witness_edge_query c=\<lparr>query_equations=[(c,Finite_Variable 0)],query_site=82,
    query_goal=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)),
    query_element=2\<rparr>"

lemma witness_selection_query_answers:
  assumes functional: "finite_relation_functional B" and bound: "(c,t) |\<in>| B"
    and scope: "\<And>x. x |\<in>| finite_pattern_variables pe \<Longrightarrow> x\<noteq>3 \<and> x\<noteq>4" and list: "l\<noteq>3" "l\<noteq>4"
  shows "decode_finite_term ` {e. finite_query_holds P (witness_selection_query c pe l) B [] e}=
    {d. \<exists>\<sigma>. resolution_value \<sigma> pe=t \<and>
      d \<in> selection_answers (positive_meaning (decode_finite_system P)) (decode_finite_term (\<sigma> l))}"
    (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix d assume "d \<in> ?L"
    then obtain e where d: "d=decode_finite_term e"
      and holds: "finite_query_holds P (witness_selection_query c pe l) B [] e" by blast
    obtain \<theta> where \<theta>: "resolution_value \<theta> pe=t" "\<theta> 3=e"
      "(5,Pair_Term (decode_finite_term (\<theta> 3)) (Pair_Term (decode_finite_term (\<theta> l)) (decode_finite_term (\<theta> 4))))
        \<in> positive_meaning (decode_finite_system P)"
      using holds unfolding witness_selection_query_def finite_query_holds_equation[OF functional bound] by auto
    show "d \<in> ?R" using \<theta> d by (intro CollectI exI[of _ \<theta>] conjI) auto
  qed
  show "?R \<subseteq> ?L"
  proof
    fix d assume "d \<in> ?R"
    then obtain \<sigma> r where \<sigma>: "resolution_value \<sigma> pe=t"
      and sel: "(5,Pair_Term d (Pair_Term (decode_finite_term (\<sigma> l)) r)) \<in> positive_meaning (decode_finite_system P)"
      by blast
    have formed: "term_formed d" "term_formed r"
      using schema_call_formed_target[OF positive_meaning_formed[OF sel]] by simp_all
    define \<theta> where "\<theta>=\<sigma>(3:=finite_term_of d,4:=finite_term_of r)"
    have agree: "resolution_value \<theta> pe=resolution_value \<sigma> pe"
    proof (rule resolution_value_cong)
      fix x assume "x |\<in>| finite_pattern_variables pe"
      then show "\<theta> x=\<sigma> x" using scope by (simp add: \<theta>_def)
    qed
    have vals: "decode_finite_term (\<theta> 3)=d" "decode_finite_term (\<theta> 4)=r" "\<theta> l=\<sigma> l"
      using formed list by (simp_all add: \<theta>_def decode_finite_term_of)
    have "finite_query_holds P (witness_selection_query c pe l) B [] (\<theta> 3)"
      unfolding witness_selection_query_def finite_query_holds_equation[OF functional bound]
      by (rule exI[of _ \<theta>]) (use \<sigma> agree vals sel in simp)
    then show "d \<in> ?L" using vals(1) by (intro image_eqI[of _ _ "\<theta> 3"]) simp_all
  qed
qed

lemma witness_edge_query_answers:
  assumes functional: "finite_relation_functional B" and bound: "(c,t) |\<in>| B"
  shows "map_prod decode_finite_term decode_finite_term `
      {(f,e). finite_query_holds P (witness_edge_query c) B [(f,Finite_Variable 1)] e}=
    edge_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t)"
    (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix z assume "z \<in> ?L"
    then obtain f e where z: "z=(decode_finite_term f,decode_finite_term e)"
      and holds: "finite_query_holds P (witness_edge_query c) B [(f,Finite_Variable 1)] e" by auto
    obtain \<theta> :: "nat \<Rightarrow> finite_factor_term" where \<theta>: "\<theta> 0=t" "\<theta> 1=f" "\<theta> 2=e"
      "(82,Pair_Term (decode_finite_term (\<theta> 0)) (Pair_Term (decode_finite_term (\<theta> 1)) (decode_finite_term (\<theta> 2))))
        \<in> positive_meaning (decode_finite_system P)"
      using holds unfolding witness_edge_query_def finite_query_holds_equation[OF functional bound] by auto
    show "z \<in> ?R" using \<theta> z by simp
  qed
  show "?R \<subseteq> ?L"
  proof
    fix z assume "z \<in> ?R"
    then obtain a b where z: "z=(a,b)"
      and edge: "(82,Pair_Term (decode_finite_term t) (Pair_Term a b)) \<in> positive_meaning (decode_finite_system P)"
      by auto
    have formed: "term_formed a" "term_formed b"
      using schema_call_formed_target[OF positive_meaning_formed[OF edge]] by simp_all
    define \<theta> :: "nat \<Rightarrow> finite_factor_term" where
      "\<theta>=(\<lambda>v. if v=0 then t else if v=1 then finite_term_of a else finite_term_of b)"
    have "finite_query_holds P (witness_edge_query c) B [(finite_term_of a,Finite_Variable 1)] (finite_term_of b)"
      unfolding witness_edge_query_def finite_query_holds_equation[OF functional bound]
      by (rule exI[of _ \<theta>]) (use edge formed in \<open>simp add: \<theta>_def decode_finite_term_of\<close>)
    then show "z \<in> ?L" using formed z
      by (intro image_eqI[of _ _ "(finite_term_of a,finite_term_of b)"]) (simp_all add: decode_finite_term_of)
  qed
qed

subsection \<open>The closure family: the reach of the roots over the definition edges\<close>

definition closure_witness_family :: "'a \<Rightarrow> 'a \<Rightarrow> ('a,nat,nat) collection_family" where
  "closure_witness_family env root=\<lparr>family_base=[witness_selection_query root (Finite_Variable 0) 0],
    family_step=Some (witness_edge_query env,Finite_Variable 1),family_key=(Finite_Variable 0,0),family_identity=None\<rparr>"

theorem closure_witness_family_elements:
  assumes functional: "finite_relation_functional B" and env: "(env,tx) |\<in>| B" and root: "(root,ty) |\<in>| B"
    and collect: "finite_family_collection P n (closure_witness_family env root) B=Some (es,cs)"
  shows "decode_finite_term ` fst ` set es=
    least_closure_bound (positive_meaning (decode_finite_system P)) (decode_finite_term tx) (decode_finite_term ty)"
proof -
  let ?M="positive_meaning (decode_finite_system P)"
  let ?F="closure_witness_family env root"
  have elements: "fst ` set es=(finite_family_step_answers P ?F B)\<^sup>* `` finite_family_base_answers P ?F B"
    by (rule finite_family_collection_exact[OF collect]) (simp add: closure_witness_family_def)
  have base_set: "finite_family_base_answers P ?F B=
      {e. finite_query_holds P (witness_selection_query root (Finite_Variable 0) 0) B [] e}"
    by (simp add: finite_family_base_answers_def closure_witness_family_def)
  have selected: "decode_finite_term ` {e. finite_query_holds P (witness_selection_query root (Finite_Variable 0) 0) B [] e}=
      {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Variable (0::nat))=ty \<and> d \<in> selection_answers ?M (decode_finite_term (\<sigma> 0))}"
    by (rule witness_selection_query_answers[OF functional root]) simp_all
  have roots: "{d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Variable (0::nat))=ty \<and> d \<in> selection_answers ?M (decode_finite_term (\<sigma> 0))}=
      selection_answers ?M (decode_finite_term ty)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Variable (0::nat))=ty \<and>
      d \<in> selection_answers ?M (decode_finite_term (\<sigma> 0))}"
    then show "d \<in> selection_answers ?M (decode_finite_term ty)" by auto
  next
    fix d assume "d \<in> selection_answers ?M (decode_finite_term ty)"
    then show "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Variable (0::nat))=ty \<and>
      d \<in> selection_answers ?M (decode_finite_term (\<sigma> 0))}"
      by (intro CollectI exI[of _ "\<lambda>_. ty"]) simp
  qed
  have step_set: "finite_family_step_answers P ?F B=
      {(f,e). finite_query_holds P (witness_edge_query env) B [(f,Finite_Variable 1)] e}"
    by (simp add: finite_family_step_answers_def closure_witness_family_def)
  have inj: "inj decode_finite_term" by (rule injI) simp
  show ?thesis
    by (simp only: elements rtrancl_injective_image_set[OF inj, symmetric] base_set step_set selected roots
      witness_edge_query_answers[OF functional env])
qed

definition closure_witness_registration :: "nat \<Rightarrow> (nat,nat,nat) factor_schema \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (nat,nat,nat,nat) collection_registration" where
  "closure_witness_registration d S a env root=\<lparr>registration_site=d,registration_schema=finite_schema_of S,
    registration_variable=a,registration_families=Single_Family (closure_witness_family env root)\<rparr>"

theorem closure_witness_registration_value:
  assumes functional: "finite_relation_functional B" and env: "(env,tx) |\<in>| B" and root: "(root,ty) |\<in>| B"
    and valued: "finite_registration_value P n (closure_witness_registration d S a env root) B=Some v"
  shows "finite_term_formed v"
    and "\<exists>zs. decode_finite_term v=data_list_term zs \<and>
      set zs=least_closure_bound (positive_meaning (decode_finite_system P)) (decode_finite_term tx) (decode_finite_term ty)"
proof -
  show "finite_term_formed v" by (rule finite_registration_value_formed[OF valued])
  obtain es cs where collect: "finite_family_collection P n (closure_witness_family env root) B=Some (es,cs)"
    and v: "v=finite_family_value es"
    using valued by (auto simp: finite_registration_value_def closure_witness_registration_def finite_family_collected_some)
  have "set (map (decode_finite_term \<circ> fst) es)=decode_finite_term ` fst ` set es" by (simp only: set_map image_comp)
  then show "\<exists>zs. decode_finite_term v=data_list_term zs \<and>
      set zs=least_closure_bound (positive_meaning (decode_finite_system P)) (decode_finite_term tx) (decode_finite_term ty)"
    using closure_witness_family_elements[OF functional env root collect] finite_family_value_presents[of es] v
    by (intro exI[of _ "map (decode_finite_term \<circ> fst) es"]) simp
qed

subsection \<open>77's bound and the additions notion's bound\<close>

definition bound_witness_registration :: "(nat,nat,nat,nat) collection_registration" where
  "bound_witness_registration=closure_witness_registration 77 package_closure_admission_schema 2 0 1"

definition additions_witness_registration :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat,nat) collection_registration" where
  "additions_witness_registration entry_site list_site=
    closure_witness_registration entry_site (package_additions_schema list_site) 5 1 4"

lemma bound_witness_premises_hold:
  "finite_variable_premises_hold P (finite_schema_of package_closure_admission_schema) 2 \<theta> \<longleftrightarrow>
    (47,Pair_Term (decode_finite_term (\<theta> 1)) (decode_finite_term (\<theta> 2))) \<in> positive_meaning (decode_finite_system P) \<and>
    (76,Pair_Term (Pair_Term (decode_finite_term (\<theta> 0)) (decode_finite_term (\<theta> 2))) (decode_finite_term (\<theta> 2)))
      \<in> positive_meaning (decode_finite_system P)"
  by (simp add: finite_variable_premises_hold_def finite_schema_of_premises_member finite_schema_of_materials_member
    package_closure_admission_schema_def all_conj_distrib)

lemma additions_witness_premises_hold:
  "finite_variable_premises_hold P (finite_schema_of (package_additions_schema l)) 5 \<theta> \<longleftrightarrow>
    (47,Pair_Term (decode_finite_term (\<theta> 4)) (decode_finite_term (\<theta> 5))) \<in> positive_meaning (decode_finite_system P) \<and>
    (76,Pair_Term (Pair_Term (decode_finite_term (\<theta> 1)) (decode_finite_term (\<theta> 5))) (decode_finite_term (\<theta> 5)))
      \<in> positive_meaning (decode_finite_system P) \<and>
    (l,Pair_Term (Pair_Term (decode_finite_term (\<theta> 0)) (Pair_Term (decode_finite_term (\<theta> 1))
      (Pair_Term (decode_finite_term (\<theta> 2)) (decode_finite_term (\<theta> 3))))) (decode_finite_term (\<theta> 5)))
      \<in> positive_meaning (decode_finite_system P)"
  by (simp add: finite_variable_premises_hold_def finite_schema_of_premises_member finite_schema_of_materials_member
    package_additions_schema_def all_conj_distrib)

theorem bound_witness_registration_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (82,t)\<in>positive_meaning definition_edge_reading_system"
    and subset: "\<And>t. (47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (76,t)\<in>positive_meaning definition_callee_list_system"
  shows "finite_registration_complete P n bound_witness_registration"
proof -
  let ?S="finite_schema_of package_closure_admission_schema"
  let ?M="positive_meaning (decode_finite_system P)"
  have fields: "registration_schema bound_witness_registration=?S" "registration_variable bound_witness_registration=2"
    by (simp_all add: bound_witness_registration_def closure_witness_registration_def)
  have head: "2 |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    by (simp add: finite_schema_of_def package_closure_admission_schema_def)
  have complete: "finite_value_complete P ?S 2 (finite_registration_value P n bound_witness_registration)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume functional: "finite_relation_functional B" and "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and "2 |\<notin>| fimage fst B" and scope: "finite_variable_premises_bound ?S 2 (fimage fst B)"
      and valued: "finite_registration_value P n bound_witness_registration B=Some v"
    have "0 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=2 and e=76 and
        p="Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2)) (Finite_Variable 2)"])
        (simp_all add: finite_schema_of_premises_member package_closure_admission_schema_def)
    then obtain tx where tx: "(0,tx) |\<in>| B" by (rule fimage_fst_binding)
    have "1 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=1 and e=47 and
        p="Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)"])
        (simp_all add: finite_schema_of_premises_member package_closure_admission_schema_def)
    then obtain ty where ty: "(1,ty) |\<in>| B" by (rule fimage_fst_binding)
    have binding: "finite_binding_valuation B 0=tx" "finite_binding_valuation B 1=ty"
      by (rule finite_binding_valuation_member[OF functional tx], rule finite_binding_valuation_member[OF functional ty])
    note valued'=valued[unfolded bound_witness_registration_def]
    obtain zs where zs: "decode_finite_term v=data_list_term zs"
      "set zs=least_closure_bound ?M (decode_finite_term tx) (decode_finite_term ty)"
      using closure_witness_registration_value(2)[OF functional tx ty valued'] by blast
    have formed: "finite_term_formed v" by (rule closure_witness_registration_value(1)[OF functional tx ty valued'])
    have hold: "finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=w)) \<longleftrightarrow>
        (47,Pair_Term (decode_finite_term ty) (decode_finite_term w)) \<in> ?M \<and>
        (76,Pair_Term (Pair_Term (decode_finite_term tx) (decode_finite_term w)) (decode_finite_term w)) \<in> ?M" for w
      by (simp add: bound_witness_premises_hold binding[simplified])
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=v))"
    proof
      assume "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=w))"
      then obtain w where held: "(47,Pair_Term (decode_finite_term ty) (decode_finite_term w)) \<in> ?M"
        "(76,Pair_Term (Pair_Term (decode_finite_term tx) (decode_finite_term w)) (decode_finite_term w)) \<in> ?M"
        by (auto simp: hold)
      obtain ys where "decode_finite_term w=data_list_term ys" "set zs\<subseteq>set ys"
          "(47,Pair_Term (decode_finite_term ty) (data_list_term zs)) \<in> ?M"
          "(76,Pair_Term (Pair_Term (decode_finite_term tx) (data_list_term zs)) (data_list_term zs)) \<in> ?M"
        by (rule closed_bound_least[OF selection edges subset bound zs(2) held])
      then show "finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=v))" by (simp add: hold zs(1))
    next
      assume "finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=v))"
      then show "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 2 ((finite_binding_valuation B)(2:=w))"
        using formed by blast
    qed
  qed
  show ?thesis unfolding finite_registration_complete_def fields using head complete by simp
qed

theorem additions_witness_registration_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (82,t)\<in>positive_meaning definition_edge_reading_system"
    and subset: "\<And>t. (47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (76,t)\<in>positive_meaning definition_callee_list_system"
    and listing: "context_list_rule_relation (positive_meaning (decode_finite_system P)) element_site list_site"
  shows "finite_registration_complete P n (additions_witness_registration entry_site list_site)"
proof -
  let ?S="finite_schema_of (package_additions_schema list_site)"
  let ?R="additions_witness_registration entry_site list_site"
  let ?M="positive_meaning (decode_finite_system P)"
  have fields: "registration_schema ?R=?S" "registration_variable ?R=5"
    by (simp_all add: additions_witness_registration_def closure_witness_registration_def)
  have head: "5 |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    by (simp add: finite_schema_of_def package_additions_schema_def)
  have complete: "finite_value_complete P ?S 5 (finite_registration_value P n ?R)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume functional: "finite_relation_functional B" and "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and "5 |\<notin>| fimage fst B" and scope: "finite_variable_premises_bound ?S 5 (fimage fst B)"
      and valued: "finite_registration_value P n ?R B=Some v"
    have "1 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=4 and e=76 and
        p="Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 5)) (Finite_Variable 5)"])
        (simp_all add: finite_schema_of_premises_member package_additions_schema_def)
    then obtain ty where ty: "(1,ty) |\<in>| B" by (rule fimage_fst_binding)
    have "4 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=3 and e=47 and
        p="Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 5)"])
        (simp_all add: finite_schema_of_premises_member package_additions_schema_def)
    then obtain tr where tr: "(4,tr) |\<in>| B" by (rule fimage_fst_binding)
    have binding: "finite_binding_valuation B 1=ty" "finite_binding_valuation B 4=tr"
      by (rule finite_binding_valuation_member[OF functional ty], rule finite_binding_valuation_member[OF functional tr])
    note valued'=valued[unfolded additions_witness_registration_def]
    obtain zs where zs: "decode_finite_term v=data_list_term zs"
      "set zs=least_closure_bound ?M (decode_finite_term ty) (decode_finite_term tr)"
      using closure_witness_registration_value(2)[OF functional ty tr valued'] by blast
    have formed: "finite_term_formed v" by (rule closure_witness_registration_value(1)[OF functional ty tr valued'])
    let ?c="Pair_Term (decode_finite_term (finite_binding_valuation B 0)) (Pair_Term (decode_finite_term ty)
      (Pair_Term (decode_finite_term (finite_binding_valuation B 2)) (decode_finite_term (finite_binding_valuation B 3))))"
    have hold: "finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=w)) \<longleftrightarrow>
        (47,Pair_Term (decode_finite_term tr) (decode_finite_term w)) \<in> ?M \<and>
        (76,Pair_Term (Pair_Term (decode_finite_term ty) (decode_finite_term w)) (decode_finite_term w)) \<in> ?M \<and>
        (list_site,Pair_Term ?c (decode_finite_term w)) \<in> ?M" for w
      by (simp add: additions_witness_premises_hold binding[simplified])
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=v))"
    proof
      assume "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=w))"
      then obtain w where held: "(47,Pair_Term (decode_finite_term tr) (decode_finite_term w)) \<in> ?M"
        "(76,Pair_Term (Pair_Term (decode_finite_term ty) (decode_finite_term w)) (decode_finite_term w)) \<in> ?M"
        "(list_site,Pair_Term ?c (decode_finite_term w)) \<in> ?M"
        by (auto simp: hold)
      obtain ys where least: "decode_finite_term w=data_list_term ys" "set zs\<subseteq>set ys"
          "(47,Pair_Term (decode_finite_term tr) (data_list_term zs)) \<in> ?M"
          "(76,Pair_Term (Pair_Term (decode_finite_term ty) (data_list_term zs)) (data_list_term zs)) \<in> ?M"
        by (rule closed_bound_least[OF selection edges subset bound zs(2) held(1,2)])
      have "(list_site,Pair_Term ?c (data_list_term zs)) \<in> ?M"
        by (rule context_list_rule_relation.elements_antimono[OF listing held(3)[unfolded least(1)] least(2)])
      then show "finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=v))"
        using least(3,4) by (simp add: hold zs(1))
    next
      assume "finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=v))"
      then show "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 5 ((finite_binding_valuation B)(5:=w))"
        using formed by blast
    qed
  qed
  show ?thesis unfolding finite_registration_complete_def fields using head complete by simp
qed

subsection \<open>561's private environment: the rows of the two environments\<close>

text \<open>
  Each family answers the rows of one table of the two environment values, each value matched as the pair of its two
  tables: its key is a row's first component (an artifact row's use, a binding row's use and slot), artifact rows of
  one key identified by artifact identity (12) and binding rows by equality. With no conflict the two lists present
  the merge (@{text merge_witness_registration_value}); a conflict certifies incompatibility.
\<close>

definition artifact_row_witness_identity :: "(nat,nat) collection_identity" where
  "artifact_row_witness_identity=\<lparr>identity_left=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    identity_right=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2),identity_site=12,
    identity_goal=Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2)\<rparr>"

definition row_witness_family ::
    "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat,nat) collection_identity option \<Rightarrow> ('a,nat,nat) collection_family" where
  "row_witness_family c c' l I=\<lparr>family_base=
      [witness_selection_query c (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) l,
       witness_selection_query c' (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) l],
    family_step=None,family_key=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),0),family_identity=I\<rparr>"

definition merge_witness_registration :: "(nat,nat,nat,nat) collection_registration" where
  "merge_witness_registration=\<lparr>registration_site=561,registration_schema=finite_schema_of package_request_schema,
    registration_variable=7,registration_families=Paired_Families
      (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) (row_witness_family 0 4 1 None)\<rparr>"

lemma pair_selection_answers:
  "{d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 0))}=artifact_row_answers M (decode_finite_term t)"
  "{d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 1))}=binding_row_answers M (decode_finite_term t)"
proof -
  show "{d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 0))}=artifact_row_answers M (decode_finite_term t)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 0))}"
    then obtain \<sigma> :: "nat \<Rightarrow> finite_factor_term" where "Finite_Pair (\<sigma> 0) (\<sigma> 1)=t"
      "d \<in> selection_answers M (decode_finite_term (\<sigma> 0))" by auto
    then show "d \<in> artifact_row_answers M (decode_finite_term t)" by auto
  next
    fix d assume "d \<in> artifact_row_answers M (decode_finite_term t)"
    then obtain fa fb where "t=Finite_Pair fa fb" "d \<in> selection_answers M (decode_finite_term fa)"
      by (auto simp: decode_finite_pair_iff)
    then show "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 0))}"
      by (intro CollectI exI[of _ "\<lambda>v. if v=0 then fa else fb"]) simp
  qed
  show "{d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 1))}=binding_row_answers M (decode_finite_term t)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 1))}"
    then obtain \<sigma> :: "nat \<Rightarrow> finite_factor_term" where "Finite_Pair (\<sigma> 0) (\<sigma> 1)=t"
      "d \<in> selection_answers M (decode_finite_term (\<sigma> 1))" by auto
    then show "d \<in> binding_row_answers M (decode_finite_term t)" by auto
  next
    fix d assume "d \<in> binding_row_answers M (decode_finite_term t)"
    then obtain fa fb where "t=Finite_Pair fa fb" "d \<in> selection_answers M (decode_finite_term fb)"
      by (auto simp: decode_finite_pair_iff)
    then show "d \<in> {d. \<exists>\<sigma>. resolution_value \<sigma> (Finite_Pattern_Pair (Finite_Variable (0::nat)) (Finite_Variable 1))=t \<and>
      d \<in> selection_answers M (decode_finite_term (\<sigma> 1))}"
      by (intro CollectI exI[of _ "\<lambda>v. if v=0 then fa else fb"]) simp
  qed
qed

lemma row_witness_family_base:
  assumes functional: "finite_relation_functional B" and left: "(c,t) |\<in>| B" and right: "(c',t') |\<in>| B"
  shows "decode_finite_term ` finite_family_base_answers P (row_witness_family c c' 0 I) B=
      artifact_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t) \<union>
      artifact_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t')"
    and "decode_finite_term ` finite_family_base_answers P (row_witness_family c c' 1 I) B=
      binding_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t) \<union>
      binding_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t')"
proof -
  let ?p="Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable (1::nat))"
  have split: "finite_family_base_answers P (row_witness_family c c' l I) B=
      {e. finite_query_holds P (witness_selection_query c ?p l) B [] e} \<union>
      {e. finite_query_holds P (witness_selection_query c' ?p l) B [] e}" for l
    by (auto simp: finite_family_base_answers_def row_witness_family_def)
  have scope: "x\<noteq>3 \<and> x\<noteq>4" if "x |\<in>| finite_pattern_variables ?p" for x using that by auto
  have artifacts: "decode_finite_term ` {e. finite_query_holds P (witness_selection_query b ?p 0) B [] e}=
      artifact_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term u)"
    if bound: "(b,u) |\<in>| B" for b u
    by (rule trans[OF witness_selection_query_answers[OF functional bound scope, where l=0] pair_selection_answers(1)])
      simp_all
  have bindings: "decode_finite_term ` {e. finite_query_holds P (witness_selection_query b ?p 1) B [] e}=
      binding_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term u)"
    if bound: "(b,u) |\<in>| B" for b u
    by (rule trans[OF witness_selection_query_answers[OF functional bound scope, where l=1] pair_selection_answers(2)])
      simp_all
  show "decode_finite_term ` finite_family_base_answers P (row_witness_family c c' 0 I) B=
      artifact_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t) \<union>
      artifact_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t')"
    by (simp only: split image_Un artifacts[OF left] artifacts[OF right])
  show "decode_finite_term ` finite_family_base_answers P (row_witness_family c c' 1 I) B=
      binding_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t) \<union>
      binding_row_answers (positive_meaning (decode_finite_system P)) (decode_finite_term t')"
    by (simp only: split image_Un bindings[OF left] bindings[OF right])
qed

lemma row_witness_family_key: "finite_family_key (row_witness_family c c' l I) (Finite_Pair k a)=Some k"
proof -
  define \<theta> :: "nat \<Rightarrow> finite_factor_term" where "\<theta>=(\<lambda>v. if v=0 then k else a)"
  have evaluated: "\<And>t p. (t,p) \<in> set [(Finite_Pair k a,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))] \<Longrightarrow>
      finite_pattern_formed p \<and> resolution_value \<theta> p=t"
    by (auto simp: \<theta>_def)
  obtain W where W: "finite_inputs_matching [(Finite_Pair k a,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))]=
      Some W" "\<And>x u. (x,u) |\<in>| W \<Longrightarrow> \<theta> x=u"
    by (rule finite_inputs_matching_complete[where
      ts="[(Finite_Pair k a,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))]", OF evaluated],
      assumption, rule that)
  have "finite_pattern_instance W (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Pair k a)"
    by (rule finite_inputs_matching_some(2)[OF W(1)]) simp
  then have "(0,k) |\<in>| W" by simp
  then have "finite_relation_option W 0=Some k"
    using finite_relation_option_correct[OF finite_inputs_matching_some(1)[OF W(1)]] by blast
  then show ?thesis by (simp add: finite_family_key_def row_witness_family_def W(1)[simplified])
qed

theorem row_witness_family_rows:
  assumes collect: "finite_family_collection P n (row_witness_family c c' l I) B=Some (es,cs)"
    and base: "decode_finite_term ` finite_family_base_answers P (row_witness_family c c' l I) B=R"
    and pairs: "\<forall>u\<in>R. \<exists>k a. u=Pair_Term k a"
  shows "set (map (decode_finite_term \<circ> fst) es) \<subseteq> R"
    and "\<forall>u\<in>R. \<exists>u'\<in>set (map (decode_finite_term \<circ> fst) es). answer_key u'=answer_key u"
    and "cs=[] \<Longrightarrow> distinct (map answer_key (map (decode_finite_term \<circ> fst) es))"
    and "(x,y) \<in> set cs \<Longrightarrow> \<exists>k a b. x=Finite_Pair k a \<and> y=Finite_Pair k b \<and> a\<noteq>b \<and>
      decode_finite_term x \<in> R \<and> decode_finite_term y \<in> R \<and>
      \<not> finite_family_identified P (row_witness_family c c' l I) x y"
proof -
  let ?F="row_witness_family c c' l I"
  have step: "finite_family_step_answers P ?F B={}"
    by (simp add: finite_family_step_answers_def row_witness_family_def)
  have sound: "fst ` set es \<subseteq> finite_family_base_answers P ?F B"
    using finite_family_collection_sound(1)[OF collect] by (simp add: step)
  have inR: "decode_finite_term e \<in> R" if "e \<in> finite_family_base_answers P ?F B" for e
    using that base by blast
  have pair: "\<exists>k a. e=Finite_Pair k a" if member: "e \<in> finite_family_base_answers P ?F B" for e
  proof -
    obtain k a where "decode_finite_term e=Pair_Term k a" using pairs inR[OF member] by blast
    then show ?thesis by (auto simp: decode_finite_pair_iff)
  qed
  have key: "finite_family_key ?F (Finite_Pair k a)=Some k" for k a by (rule row_witness_family_key)
  show "set (map (decode_finite_term \<circ> fst) es) \<subseteq> R" using sound inR by auto
  show "\<forall>u\<in>R. \<exists>u'\<in>set (map (decode_finite_term \<circ> fst) es). answer_key u'=answer_key u"
  proof
    fix u assume "u \<in> R"
    then obtain e where e: "e \<in> finite_family_base_answers P ?F B" "u=decode_finite_term e" using base by blast
    obtain x where x: "x \<in> fst ` set es" "finite_family_key ?F x=finite_family_key ?F e"
      using finite_family_collection_complete(1)[OF collect] e(1) unfolding finite_family_covers_def by blast
    obtain ke ae where ee: "e=Finite_Pair ke ae" using pair[OF e(1)] by blast
    obtain kx ax where xx: "x=Finite_Pair kx ax" using pair sound x(1) by blast
    have "kx=ke" using x(2) by (simp add: ee xx key)
    then have keyed: "answer_key (decode_finite_term x)=answer_key u" using e(2) ee xx by simp
    obtain y where y: "y \<in> set es" "x=fst y" using x(1) by blast
    have "decode_finite_term x \<in> set (map (decode_finite_term \<circ> fst) es)"
      unfolding set_map by (rule image_eqI[of _ _ y]) (simp_all add: y)
    then show "\<exists>u'\<in>set (map (decode_finite_term \<circ> fst) es). answer_key u'=answer_key u"
      using keyed by blast
  qed
  show "distinct (map answer_key (map (decode_finite_term \<circ> fst) es))" if none: "cs=[]"
  proof -
    have keys: "distinct (map (finite_family_key ?F \<circ> fst) es)"
      by (rule finite_family_collection_keys) (use collect none in simp)
    have inj: "inj_on (answer_key \<circ> (decode_finite_term \<circ> fst)) (set es)"
    proof (rule inj_onI)
      fix y z assume y: "y \<in> set es" and z: "z \<in> set es"
        and same: "(answer_key \<circ> (decode_finite_term \<circ> fst)) y=(answer_key \<circ> (decode_finite_term \<circ> fst)) z"
      obtain ky ay where yy: "fst y=Finite_Pair ky ay" using pair sound y by blast
      obtain kz az where zz: "fst z=Finite_Pair kz az" using pair sound z by blast
      have "(finite_family_key ?F \<circ> fst) y=(finite_family_key ?F \<circ> fst) z" using same by (simp add: yy zz key)
      then show "y=z" using keys y z by (auto simp: distinct_map inj_on_def)
    qed
    show ?thesis using keys inj by (simp add: distinct_map)
  qed
  show "\<exists>k a b. x=Finite_Pair k a \<and> y=Finite_Pair k b \<and> a\<noteq>b \<and>
      decode_finite_term x \<in> R \<and> decode_finite_term y \<in> R \<and> \<not> finite_family_identified P ?F x y"
    if conflict: "(x,y) \<in> set cs"
  proof -
    note c=finite_family_collection_conflicts[OF collect conflict]
    obtain kx ax where xx: "x=Finite_Pair kx ax" using pair sound c(1) by blast
    obtain ky ay where yy: "y=Finite_Pair ky ay" using pair sound c(2) by blast
    have same: "kx=ky" using c(3) by (simp add: xx yy key)
    have apart: "ax\<noteq>ay" using c(4) same by (simp add: xx yy)
    show ?thesis using c(1,2,5) sound inR xx yy same apart by blast
  qed
qed

lemma artifact_row_witness_identity_holds:
  assumes "(12,Pair_Term (decode_finite_term a) (decode_finite_term b)) \<in> positive_meaning (decode_finite_system P)"
  shows "finite_identity_holds P artifact_row_witness_identity (Finite_Pair k a) (Finite_Pair k b)"
  unfolding finite_identity_holds_def artifact_row_witness_identity_def
  by (rule exI[of _ "\<lambda>v. if v=0 then k else if v=1 then a else b"]) (use assms in simp)

theorem merge_witness_registration_value:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (12,t)\<in>positive_meaning artifact_identity_system"
    and functional: "finite_relation_functional B" and left: "(0,tx) |\<in>| B" and right: "(4,tv) |\<in>| B"
    and valued: "finite_registration_value P n merge_witness_registration B=Some v"
    and sources: "environment_value_presents E (decode_finite_term tx)" "environment_value_presents F (decode_finite_term tv)"
    and compatible: "environments_compatible E F"
  shows "environment_value_presents (merge_environment E F) (decode_finite_term v)"
proof -
  let ?M="positive_meaning (decode_finite_system P)"
  let ?x="decode_finite_term tx" and ?y="decode_finite_term tv"
  have free: "\<not> row_answers_conflict ?M ?x ?y"
    using environment_row_conflict[OF selection identity sources] compatible by blast
  obtain esA csA esB csB
    where A: "finite_family_collection P n (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) B=Some (esA,csA)"
      and Bc: "finite_family_collection P n (row_witness_family 0 4 1 None) B=Some (esB,csB)"
      and v: "v=Finite_Pair (finite_family_value esA) (finite_family_value esB)"
    using valued by (auto simp: finite_registration_value_def merge_witness_registration_def finite_family_collected_some
      split: option.splits)
  have baseA: "decode_finite_term ` finite_family_base_answers P (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) B=
      artifact_row_answers ?M ?x \<union> artifact_row_answers ?M ?y"
    by (rule row_witness_family_base(1)[OF functional left right])
  have baseB: "decode_finite_term ` finite_family_base_answers P (row_witness_family 0 4 1 None) B=
      binding_row_answers ?M ?x \<union> binding_row_answers ?M ?y"
    by (rule row_witness_family_base(2)[OF functional left right])
  have pairsA: "\<forall>u\<in>artifact_row_answers ?M ?x \<union> artifact_row_answers ?M ?y. \<exists>k a. u=Pair_Term k a"
  proof
    fix u assume "u \<in> artifact_row_answers ?M ?x \<union> artifact_row_answers ?M ?y"
    then obtain z where "environment_artifact_entry_presents z u"
      using environment_value_answers(1)[OF selection sources(1)] environment_value_answers(1)[OF selection sources(2)]
      by blast
    then show "\<exists>k a. u=Pair_Term k a" by (auto simp: environment_artifact_entry_presents_def)
  qed
  have pairsB: "\<forall>u\<in>binding_row_answers ?M ?x \<union> binding_row_answers ?M ?y. \<exists>k a. u=Pair_Term k a"
    by (simp only: environment_value_answers(3)[OF selection sources(1)] environment_value_answers(3)[OF selection sources(2)])
      (auto simp: binding_data_def)
  note rowsA=row_witness_family_rows[OF A baseA pairsA]
  note rowsB=row_witness_family_rows[OF Bc baseB pairsB]
  have noneA: "csA=[]"
  proof (rule ccontr)
    assume "csA\<noteq>[]"
    then obtain x y where conflict: "(x,y) \<in> set csA" by (cases csA) auto
    obtain k a b where c: "x=Finite_Pair k a" "y=Finite_Pair k b"
      "decode_finite_term x \<in> artifact_row_answers ?M ?x \<union> artifact_row_answers ?M ?y"
      "decode_finite_term y \<in> artifact_row_answers ?M ?x \<union> artifact_row_answers ?M ?y"
      "\<not> finite_family_identified P (row_witness_family 0 4 0 (Some artifact_row_witness_identity)) x y"
      using rowsA(4)[OF conflict] by blast
    have "(12,Pair_Term (decode_finite_term a) (decode_finite_term b)) \<notin> ?M"
      using c(5) artifact_row_witness_identity_holds[of a b P k]
      by (auto simp: finite_family_identified_def row_witness_family_def c(1,2))
    then have "row_answers_conflict ?M ?x ?y"
      unfolding row_answers_conflict_def
      by (intro disjI1 exI[of _ "decode_finite_term k"] exI[of _ "decode_finite_term a"]
        exI[of _ "decode_finite_term b"] conjI) (use c(3,4) in \<open>simp_all add: c(1,2)\<close>)
    then show False using free by blast
  qed
  have noneB: "csB=[]"
  proof (rule ccontr)
    assume "csB\<noteq>[]"
    then obtain x y where conflict: "(x,y) \<in> set csB" by (cases csB) auto
    obtain k a b where c: "x=Finite_Pair k a" "y=Finite_Pair k b" "a\<noteq>b"
      "decode_finite_term x \<in> binding_row_answers ?M ?x \<union> binding_row_answers ?M ?y"
      "decode_finite_term y \<in> binding_row_answers ?M ?x \<union> binding_row_answers ?M ?y"
      using rowsB(4)[OF conflict] by blast
    have "row_answers_conflict ?M ?x ?y"
      unfolding row_answers_conflict_def
      by (intro disjI2 exI[of _ "decode_finite_term k"] exI[of _ "decode_finite_term a"]
        exI[of _ "decode_finite_term b"] conjI) (use c(3,4,5) in \<open>simp_all add: c(1,2)\<close>)
    then show False using free by blast
  qed
  have presented: "environment_value_presents (merge_environment E F)
      (Pair_Term (data_list_term (map (decode_finite_term \<circ> fst) esA)) (data_list_term (map (decode_finite_term \<circ> fst) esB)))"
    by (rule merge_rows_presented[OF selection identity sources free rowsA(1) rowsA(3)[OF noneA] rowsA(2)
      rowsB(1) rowsB(3)[OF noneB] rowsB(2)])
  then show ?thesis by (simp add: v finite_family_value_presents)
qed

lemma merge_witness_premises_hold:
  "finite_variable_premises_hold P (finite_schema_of package_request_schema) 7 \<theta> \<longleftrightarrow>
    (113,Pair_Term (decode_finite_term (\<theta> 0)) (decode_finite_term (\<theta> 7))) \<in> positive_meaning (decode_finite_system P) \<and>
    (113,Pair_Term (decode_finite_term (\<theta> 4)) (decode_finite_term (\<theta> 7))) \<in> positive_meaning (decode_finite_system P)"
  by (simp add: finite_variable_premises_hold_def finite_schema_of_premises_member finite_schema_of_materials_member
    package_request_schema_def all_conj_distrib)

theorem merge_witness_registration_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (12,t)\<in>positive_meaning artifact_identity_system"
    and inclusion: "\<And>t. (113,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (113,t)\<in>positive_meaning environment_inclusion_system"
  shows "finite_registration_complete P n merge_witness_registration"
proof -
  let ?S="finite_schema_of package_request_schema"
  let ?M="positive_meaning (decode_finite_system P)"
  have fields: "registration_schema merge_witness_registration=?S" "registration_variable merge_witness_registration=7"
    by (simp_all add: merge_witness_registration_def)
  have head: "7 |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    by (simp add: finite_schema_of_def package_request_schema_def)
  have complete: "finite_value_complete P ?S 7 (finite_registration_value P n merge_witness_registration)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume functional: "finite_relation_functional B" and "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and "7 |\<notin>| fimage fst B" and scope: "finite_variable_premises_bound ?S 7 (fimage fst B)"
      and valued: "finite_registration_value P n merge_witness_registration B=Some v"
    have "0 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=4 and e=113 and
        p="Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 7)"])
        (simp_all add: finite_schema_of_premises_member package_request_schema_def)
    then obtain tx where tx: "(0,tx) |\<in>| B" by (rule fimage_fst_binding)
    have "4 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=5 and e=113 and
        p="Finite_Pattern_Pair (Finite_Variable 4) (Finite_Variable 7)"])
        (simp_all add: finite_schema_of_premises_member package_request_schema_def)
    then obtain tv where tv: "(4,tv) |\<in>| B" by (rule fimage_fst_binding)
    have binding: "finite_binding_valuation B 0=tx" "finite_binding_valuation B 4=tv"
      by (rule finite_binding_valuation_member[OF functional tx], rule finite_binding_valuation_member[OF functional tv])
    have formed: "finite_term_formed v" by (rule finite_registration_value_formed[OF valued])
    have hold: "finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=w)) \<longleftrightarrow>
        (113,Pair_Term (decode_finite_term tx) (decode_finite_term w)) \<in> ?M \<and>
        (113,Pair_Term (decode_finite_term tv) (decode_finite_term w)) \<in> ?M" for w
      by (simp add: merge_witness_premises_hold binding[simplified])
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=v))"
    proof
      assume "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=w))"
      then obtain w where held: "(113,Pair_Term (decode_finite_term tx) (decode_finite_term w)) \<in> ?M"
        "(113,Pair_Term (decode_finite_term tv) (decode_finite_term w)) \<in> ?M"
        by (auto simp: hold)
      obtain E F where sources: "environment_value_presents E (decode_finite_term tx)"
          "environment_value_presents F (decode_finite_term tv)" and compatible: "environments_compatible E F"
        using merge_least_witness(1)[OF inclusion] held by blast
      have merged: "environment_value_presents (merge_environment E F) (decode_finite_term v)"
        by (rule merge_witness_registration_value[OF selection identity functional tx tv valued sources compatible])
      have "(113,Pair_Term (decode_finite_term tx) (decode_finite_term v)) \<in> ?M \<and>
          (113,Pair_Term (decode_finite_term tv) (decode_finite_term v)) \<in> ?M"
        using merge_least_witness(2)[OF inclusion sources merged] held by blast
      then show "finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=v))" by (simp add: hold)
    next
      assume "finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=v))"
      then show "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 ((finite_binding_valuation B)(7:=w))"
        using formed by blast
    qed
  qed
  show ?thesis unfolding finite_registration_complete_def fields using head complete by simp
qed

subsection \<open>The four registrations over the numbered given's readers\<close>

text \<open>
  The given's registrations: 77's bound, the additions notion's bound at the given's two list sites (392 with 391,
  525 with 524) and 561's private environment. Each is complete wherever the read sites have the numbered readers'
  meanings, so their construction is complete; they are distinct as well, which the construction does not need.
\<close>

definition given_witness_registrations :: "(nat,nat,nat,nat) collection_registration list" where
  "given_witness_registrations=[bound_witness_registration,additions_witness_registration 392 391,
    additions_witness_registration 525 524,merge_witness_registration]"

lemma given_witness_registrations_distinct: "finite_registrations_distinct given_witness_registrations"
  by (simp add: finite_registrations_distinct_def finite_registration_key_def given_witness_registrations_def
    bound_witness_registration_def additions_witness_registration_def closure_witness_registration_def
    merge_witness_registration_def)

theorem given_witness_registrations_complete:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (12,t)\<in>positive_meaning artifact_identity_system"
    and subset: "\<And>t. (47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (76,t)\<in>positive_meaning definition_callee_list_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (82,t)\<in>positive_meaning definition_edge_reading_system"
    and inclusion: "\<And>t. (113,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (113,t)\<in>positive_meaning environment_inclusion_system"
    and listing: "context_list_rule_relation (positive_meaning (decode_finite_system P)) element_391 391"
      "context_list_rule_relation (positive_meaning (decode_finite_system P)) element_524 524"
  shows "\<And>R. R \<in> set given_witness_registrations \<Longrightarrow> finite_registration_complete P n R"
    and "finite_construction_complete (finite_collection_construction given_witness_registrations n) P"
proof -
  show each: "finite_registration_complete P n R" if "R \<in> set given_witness_registrations" for R
    using that bound_witness_registration_complete[OF selection edges subset bound, of n]
      additions_witness_registration_complete[OF selection edges subset bound listing(1), of n 392]
      additions_witness_registration_complete[OF selection edges subset bound listing(2), of n 525]
      merge_witness_registration_complete[OF selection identity inclusion, of n]
    by (auto simp: given_witness_registrations_def)
  show "finite_construction_complete (finite_collection_construction given_witness_registrations n) P"
    by (rule finite_collection_construction_complete[OF each])
qed

end
