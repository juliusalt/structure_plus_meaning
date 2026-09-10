theory Factor_Schema_Renaming
  imports Factor_Interfaces
begin

section \<open>Finite changes of binder, socket, and definition coordinates\<close>

definition map_socket_graph ::
  "('s \<Rightarrow> 't) \<Rightarrow> ('d \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
    ('s \<times> ('d \<times> 'a)) set \<Rightarrow> ('t \<times> ('e \<times> 'b)) set" where
  "map_socket_graph h g f Q = (\<lambda>(s,p). (h s,map_prod g f p)) ` Q"

lemma map_socket_graph_domain:
  "rel_dom (map_socket_graph h g f Q) = h ` rel_dom Q"
  by (simp add: map_socket_graph_def pair_image_domain)

lemma map_socket_graph_finite:
  assumes "finite Q"
  shows "finite (map_socket_graph h g f Q)"
  using assms by (simp add: map_socket_graph_def)

lemma map_socket_graph_functional:
  assumes "single_valued Q" "inj_on h (rel_dom Q)"
  shows "single_valued (map_socket_graph h g f Q)"
  using single_valued_pair_image[OF assms, where g="map_prod g f"]
  by (simp add: map_socket_graph_def)

lemma map_socket_graph_member:
  "(s,d,p) \<in> map_socket_graph h g f Q \<longleftrightarrow>
    (\<exists>a b c. (a,b,c) \<in> Q \<and> s=h a \<and> d=g b \<and> p=f c)"
  by (auto simp: map_socket_graph_def map_prod_def intro: rev_image_eqI; force)

definition schema_sockets :: "('a,'s,'d) factor_schema \<Rightarrow> 's set" where
  "schema_sockets S = rel_dom (schema_premises S) \<union> rel_dom (schema_material_premises S)"

definition rename_schema ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('d \<Rightarrow> 'e) \<Rightarrow>
    ('a,'s,'d) factor_schema \<Rightarrow> ('b,'t,'e) factor_schema" where
  "rename_schema f h g S =
    \<lparr>schema_conclusion = rename_pattern f (schema_conclusion S),
     schema_premises = map_socket_graph h g (rename_pattern f) (schema_premises S),
     schema_material_premises = (\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises S\<rparr>"

lemma renamed_schema_variables:
  "schema_variables (rename_schema f h g S) = f ` schema_variables S"
  by (auto simp: schema_variables_def rename_schema_def map_socket_graph_def
      rename_pattern_variables renamed_material_variables; blast)

lemma renamed_schema_sockets:
  "schema_sockets (rename_schema f h g S) = h ` schema_sockets S"
  by (auto simp: schema_sockets_def rename_schema_def map_socket_graph_domain pair_image_domain image_Un)

lemma renamed_schema_dependencies:
  "schema_dependencies (rename_schema f h g S) = g ` schema_dependencies S"
  by (simp add: schema_dependencies_def rename_schema_def map_socket_graph_def pair_image_range image_image)

lemma renamed_schema_formed:
  assumes formed: "schema_formed S" and injective: "inj_on h (schema_sockets S)"
  shows "schema_formed (rename_schema f h g S)"
proof -
  have psv: "single_valued (schema_premises S)" and msv: "single_valued (schema_material_premises S)"
    and separate: "rel_dom (schema_premises S) \<inter> rel_dom (schema_material_premises S) = {}"
    using formed by (auto simp: schema_formed_def)
  have pinj: "inj_on h (rel_dom (schema_premises S))"
    and minj: "inj_on h (rel_dom (schema_material_premises S))"
    by (rule inj_on_subset[OF injective], auto simp: schema_sockets_def)+
  have calls: "single_valued (map_socket_graph h g (rename_pattern f) (schema_premises S))"
    by (rule map_socket_graph_functional[OF psv pinj])
  have materials: "single_valued ((\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises S)"
    by (rule single_valued_pair_image[OF msv minj])
  have apart: "h ` rel_dom (schema_premises S) \<inter> h ` rel_dom (schema_material_premises S) = {}"
    using injective separate by (auto simp: inj_on_def schema_sockets_def)
  show ?thesis using formed calls materials apart
    by (auto simp: schema_formed_def rename_schema_def map_socket_graph_def
        map_socket_graph_domain pair_image_domain)
qed

lemma renamed_schema_premise_instance:
  assumes sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and inst: "schema_premise_instance S V Q"
    and binders: "inj_on f (schema_variables S)" and sockets: "inj_on h (schema_sockets S)"
  shows "schema_premise_instance (rename_schema f h g S) (rename_term_bindings f V) (map_socket_graph h g id Q)"
proof -
  have qf: "finite Q" and qsv: "single_valued Q" and qdom: "rel_dom Q = rel_dom (schema_premises S)"
    using inst by (auto simp: schema_premise_instance_def)
  have vdom: "rel_dom V = schema_variables S" using bindings by (simp add: term_bindings_formed_def)
  have finj: "inj_on f (rel_dom V)" using binders vdom by simp
  have hinj: "inj_on h (rel_dom Q)"
    by (rule inj_on_subset[OF sockets]) (simp add: qdom schema_sockets_def)
  have finite: "finite (map_socket_graph h g id Q)" by (rule map_socket_graph_finite[OF qf])
  have functional: "single_valued (map_socket_graph h g id Q)"
    by (rule map_socket_graph_functional[OF qsv hinj])
  have domain: "rel_dom (map_socket_graph h g id Q) = rel_dom (schema_premises (rename_schema f h g S))"
    by (simp add: rename_schema_def map_socket_graph_domain qdom)
  have each: "\<And>s d p. (s,d,p) \<in> schema_premises (rename_schema f h g S) \<Longrightarrow>
    \<exists>t. (s,d,t) \<in> map_socket_graph h g id Q \<and> pattern_instance (rename_term_bindings f V) p t"
  proof -
    fix s d p assume member: "(s,d,p) \<in> schema_premises (rename_schema f h g S)"
    obtain a b c where source: "(a,b,c) \<in> schema_premises S" "s=h a" "d=g b" "p=rename_pattern f c"
      using member by (auto simp: rename_schema_def map_socket_graph_member)
    obtain t where realized: "(a,b,t) \<in> Q" "pattern_instance V c t"
      using inst source(1) unfolding schema_premise_instance_def by blast
    have scope: "pattern_variables c \<subseteq> rel_dom V"
      using source(1) vdom by (auto simp: schema_variables_def)
    have renamed: "pattern_instance (rename_term_bindings f V) (rename_pattern f c) t"
      using pattern_instance_renaming[OF finj scope] realized(2) by blast
    have target_member: "(s,d,t) \<in> map_socket_graph h g id Q"
      using source(2,3) realized(1) by (auto simp: map_socket_graph_def intro: rev_image_eqI)
    show "\<exists>t. (s,d,t) \<in> map_socket_graph h g id Q \<and> pattern_instance (rename_term_bindings f V) p t"
      using target_member renamed source(4) by blast
  qed
  show ?thesis using finite functional domain each unfolding schema_premise_instance_def by blast
qed

theorem schema_instance_renaming:
  assumes inst: "schema_instance S V t Q"
    and binders: "inj_on f (schema_variables S)" and sockets: "inj_on h (schema_sockets S)"
  shows "schema_instance (rename_schema f h g S) (rename_term_bindings f V) t (map_socket_graph h g id Q)"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def)
  have renamed: "schema_formed (rename_schema f h g S)" by (rule renamed_schema_formed[OF sf sockets])
  have new_bindings: "term_bindings_formed (schema_variables (rename_schema f h g S)) (rename_term_bindings f V)"
    using renamed_term_bindings_formed[OF bindings binders] by (simp add: renamed_schema_variables)
  have dom: "rel_dom V = schema_variables S" using bindings by (simp add: term_bindings_formed_def)
  have injective: "inj_on f (rel_dom V)" using binders dom by simp
  have scope: "pattern_variables (schema_conclusion S) \<subseteq> rel_dom V"
    using dom by (auto simp: schema_variables_def)
  have conclusion: "pattern_instance (rename_term_bindings f V) (schema_conclusion (rename_schema f h g S)) t"
    using pattern_instance_renaming[OF injective scope] head by (simp add: rename_schema_def)
  have body_result: "schema_premise_instance (rename_schema f h g S) (rename_term_bindings f V) (map_socket_graph h g id Q)"
    by (rule renamed_schema_premise_instance[OF sf bindings body binders sockets])
  show ?thesis using renamed new_bindings conclusion body_result by (simp add: schema_instance_def)
qed

theorem schema_material_satisfied_renaming:
  assumes bindings: "term_bindings_formed (schema_variables S) V"
    and injective: "inj_on f (schema_variables S)"
  shows "schema_material_satisfied (rename_schema f h g S) (rename_term_bindings f V) \<longleftrightarrow>
    schema_material_satisfied S V"
proof -
  have dom: "rel_dom V = schema_variables S" using bindings by (simp add: term_bindings_formed_def)
  have finj: "inj_on f (rel_dom V)" using injective dom by simp
  have each: "\<And>s M. (s,M) \<in> schema_material_premises S \<Longrightarrow>
    material_pattern_satisfied (rename_term_bindings f V) (rename_material_pattern f M) \<longleftrightarrow>
    material_pattern_satisfied V M"
  proof -
    fix s M assume member: "(s,M) \<in> schema_material_premises S"
    have scope: "material_variables M \<subseteq> rel_dom V"
      using member dom by (auto simp: schema_variables_def)
    show "material_pattern_satisfied (rename_term_bindings f V) (rename_material_pattern f M) \<longleftrightarrow>
      material_pattern_satisfied V M"
      by (rule material_pattern_satisfied_renaming[OF finj scope])
  qed
  show ?thesis
  proof
    assume checked: "schema_material_satisfied (rename_schema f h g S) (rename_term_bindings f V)"
    show "schema_material_satisfied S V"
    proof (unfold schema_material_satisfied_def, intro allI impI)
      fix s M assume member: "(s,M) \<in> schema_material_premises S"
      have copied: "(h s,rename_material_pattern f M) \<in> schema_material_premises (rename_schema f h g S)"
        using imageI[OF member, of "\<lambda>(s,M). (h s,rename_material_pattern f M)"]
        by (simp add: rename_schema_def)
      have result: "material_pattern_satisfied (rename_term_bindings f V) (rename_material_pattern f M)"
        using checked copied unfolding schema_material_satisfied_def by blast
      show "material_pattern_satisfied V M" using each[OF member] result by blast
    qed
  next
    assume checked: "schema_material_satisfied S V"
    show "schema_material_satisfied (rename_schema f h g S) (rename_term_bindings f V)"
    proof (unfold schema_material_satisfied_def, intro allI impI)
      fix s M assume member: "(s,M) \<in> schema_material_premises (rename_schema f h g S)"
      obtain a N where source: "(a,N) \<in> schema_material_premises S" "M=rename_material_pattern f N"
        using member by (auto simp: rename_schema_def)
      have result: "material_pattern_satisfied V N"
        using checked source(1) unfolding schema_material_satisfied_def by blast
      show "material_pattern_satisfied (rename_term_bindings f V) M"
        using each[OF source(1)] result source(2) by simp
    qed
  qed
qed

section \<open>Composition and exact cancellation of coordinate changes\<close>

lemma map_socket_graph_composition:
  "map_socket_graph h' g' f' (map_socket_graph h g f Q) =
    map_socket_graph (h' \<circ> h) (g' \<circ> g) (f' \<circ> f) Q"
  by (simp add: map_socket_graph_def map_prod_def image_image split_def comp_def)

lemma rename_schema_identity [simp]: "rename_schema id id id S = S"
  by (cases S) (simp add: rename_schema_def map_socket_graph_def map_prod_def split_def)

lemma rename_schema_composition:
  "rename_schema f' h' g' (rename_schema f h g S) =
    rename_schema (f' \<circ> f) (h' \<circ> h) (g' \<circ> g) S"
  by (simp add: rename_schema_def map_socket_graph_def map_prod_def image_image split_def
      comp_def rename_pattern_composition rename_material_composition)

lemma rename_schema_agreement:
  assumes binders: "\<forall>a\<in>schema_variables S. f a = f' a"
    and sockets: "\<forall>s\<in>schema_sockets S. h s = h' s"
    and callees: "\<forall>d\<in>schema_dependencies S. g d = g' d"
  shows "rename_schema f h g S = rename_schema f' h' g' S"
proof -
  have head: "rename_pattern f (schema_conclusion S) = rename_pattern f' (schema_conclusion S)"
    by (rule rename_pattern_agreement) (use binders in \<open>auto simp: schema_variables_def\<close>)
  have call_entries: "\<And>x. x \<in> schema_premises S \<Longrightarrow>
    (case x of (s,d,p) \<Rightarrow> (h s,g d,rename_pattern f p)) =
    (case x of (s,d,p) \<Rightarrow> (h' s,g' d,rename_pattern f' p))"
  proof -
    fix x assume member: "x \<in> schema_premises S"
    obtain s d p where shape: "x=(s,d,p)" by (cases x) auto
    have sm: "s \<in> schema_sockets S" using member shape by (auto simp: schema_sockets_def rel_dom_def)
    have dm: "d \<in> schema_dependencies S"
      using member shape by (auto simp: schema_dependencies_def rel_ran_def intro: rev_image_eqI)
    have vars: "pattern_variables p \<subseteq> schema_variables S"
      using member shape by (auto simp: schema_variables_def)
    have patterns: "rename_pattern f p = rename_pattern f' p"
      by (rule rename_pattern_agreement) (use binders vars in blast)
    show "(case x of (s,d,p) \<Rightarrow> (h s,g d,rename_pattern f p)) =
      (case x of (s,d,p) \<Rightarrow> (h' s,g' d,rename_pattern f' p))"
      using shape patterns sockets sm callees dm by simp
  qed
  have calls: "map_socket_graph h g (rename_pattern f) (schema_premises S) =
    map_socket_graph h' g' (rename_pattern f') (schema_premises S)"
    unfolding map_socket_graph_def map_prod_def
    by (rule image_cong[OF refl]) (simp add: call_entries[simplified split_def] split_def)
  have material_entries: "\<And>x. x \<in> schema_material_premises S \<Longrightarrow>
    (case x of (s,M) \<Rightarrow> (h s,rename_material_pattern f M)) =
    (case x of (s,M) \<Rightarrow> (h' s,rename_material_pattern f' M))"
  proof -
    fix x assume member: "x \<in> schema_material_premises S"
    obtain s M where shape: "x=(s,M)" by (cases x)
    have sm: "s \<in> schema_sockets S" using member shape by (auto simp: schema_sockets_def rel_dom_def)
    have vars: "material_variables M \<subseteq> schema_variables S"
      using member shape by (auto simp: schema_variables_def)
    have patterns: "rename_material_pattern f M = rename_material_pattern f' M"
      by (rule rename_material_agreement) (use binders vars in blast)
    show "(case x of (s,M) \<Rightarrow> (h s,rename_material_pattern f M)) =
      (case x of (s,M) \<Rightarrow> (h' s,rename_material_pattern f' M))"
      using shape patterns sockets sm by simp
  qed
  have materials: "(\<lambda>(s,M). (h s,rename_material_pattern f M)) ` schema_material_premises S =
    (\<lambda>(s,M). (h' s,rename_material_pattern f' M)) ` schema_material_premises S"
    by (rule image_cong[OF refl], rule material_entries; assumption)
  show ?thesis by (simp add: rename_schema_def head calls materials)
qed

theorem rename_schema_cancels:
  assumes binders: "\<forall>a\<in>schema_variables S. f' (f a) = a"
    and sockets: "\<forall>s\<in>schema_sockets S. h' (h s) = s"
    and callees: "\<forall>d\<in>schema_dependencies S. g' (g d) = d"
  shows "rename_schema f' h' g' (rename_schema f h g S) = S"
proof -
  have same: "rename_schema (f' \<circ> f) (h' \<circ> h) (g' \<circ> g) S = rename_schema id id id S"
    by (rule rename_schema_agreement) (use assms in simp_all)
  show ?thesis using same by (simp add: rename_schema_composition)
qed

text \<open>
  Binder and socket maps need only be injective on the actual finite scope.
  Callee coordinates are mapped explicitly. The complete premise graph is
  transported, while conclusion terms and every material operand value stay
  unchanged. Satisfaction remains a check of the independently fixed material
  equation, rather than a property supplied by the renaming map.
\<close>

end
