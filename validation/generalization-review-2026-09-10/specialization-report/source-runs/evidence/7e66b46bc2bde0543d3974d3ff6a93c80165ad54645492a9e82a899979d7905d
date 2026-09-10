theory Factor_Schemas
  imports Factor_Material_Patterns
begin

section \<open>Generic schemas with identified premise sockets\<close>

record ('a,'s,'d) factor_schema =
  schema_conclusion :: "'a term_pattern"
  schema_premises :: "('s \<times> ('d \<times> 'a term_pattern)) set"
  schema_material_premises :: "('s \<times> 'a material_pattern) set"

definition schema_variables :: "('a,'s,'d) factor_schema \<Rightarrow> 'a set" where
  "schema_variables S = pattern_variables (schema_conclusion S) \<union>
    (\<Union>(s,d,p)\<in>schema_premises S. pattern_variables p) \<union>
    (\<Union>(s,M)\<in>schema_material_premises S. material_variables M)"

definition schema_formed :: "('a,'s,'d) factor_schema \<Rightarrow> bool" where
  "schema_formed S \<longleftrightarrow>
    pattern_formed (schema_conclusion S) \<and> finite (schema_premises S) \<and>
    single_valued (schema_premises S) \<and>
    (\<forall>s d p. (s,d,p) \<in> schema_premises S \<longrightarrow> pattern_formed p) \<and>
    finite (schema_material_premises S) \<and> single_valued (schema_material_premises S) \<and>
    rel_dom (schema_premises S) \<inter> rel_dom (schema_material_premises S) = {} \<and>
    (\<forall>s M. (s,M) \<in> schema_material_premises S \<longrightarrow> material_pattern_formed M)"

lemma schema_variables_finite:
  assumes "schema_formed S"
  shows "finite (schema_variables S)"
proof -
  have finite: "finite (schema_premises S)" using assms by (simp add: schema_formed_def)
  have union: "finite (\<Union>(s,d,p)\<in>schema_premises S. pattern_variables p)"
    by (rule finite_UN_I[OF finite]) (auto split: prod.splits)
  have mat_finite: "finite (schema_material_premises S)" using assms by (simp add: schema_formed_def)
  have materials: "finite (\<Union>(s,M)\<in>schema_material_premises S. material_variables M)"
    by (rule finite_UN_I[OF mat_finite]) (auto split: prod.splits)
  show ?thesis using union materials by (simp add: schema_variables_def)
qed

definition schema_material_satisfied ::
  "('a,'s,'d) factor_schema \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow> bool" where
  "schema_material_satisfied S V \<longleftrightarrow>
    (\<forall>s M. (s,M) \<in> schema_material_premises S \<longrightarrow> material_pattern_satisfied V M)"

lemma empty_schema_material_satisfied:
  assumes "schema_material_premises S = {}"
  shows "schema_material_satisfied S V"
  using assms by (simp add: schema_material_satisfied_def)

definition schema_dependencies :: "('a,'s,'d) factor_schema \<Rightarrow> 'd set" where
  "schema_dependencies S = fst ` rel_ran (schema_premises S)"

lemma schema_dependencies_finite:
  assumes "schema_formed S"
  shows "finite (schema_dependencies S)"
  using assms finite_rel_ran by (auto simp: schema_dependencies_def schema_formed_def)

definition schema_premise_instance ::
  "('a,'s,'d) factor_schema \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set \<Rightarrow> bool" where
  "schema_premise_instance S V Q \<longleftrightarrow>
    finite Q \<and> single_valued Q \<and> rel_dom Q = rel_dom (schema_premises S) \<and>
    (\<forall>s d p. (s,d,p) \<in> schema_premises S \<longrightarrow>
      (\<exists>t. (s,d,t) \<in> Q \<and> pattern_instance V p t))"

definition schema_instance ::
  "('a,'s,'d) factor_schema \<Rightarrow> ('a \<times> factor_term) set \<Rightarrow> factor_term \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set \<Rightarrow> bool" where
  "schema_instance S V t Q \<longleftrightarrow>
    schema_formed S \<and> term_bindings_formed (schema_variables S) V \<and>
    pattern_instance V (schema_conclusion S) t \<and> schema_premise_instance S V Q"

lemma schema_premise_instance_origin:
  assumes inst: "schema_premise_instance S V Q" and member: "(s,d,t) \<in> Q"
  shows "\<exists>p. (s,d,p) \<in> schema_premises S \<and> pattern_instance V p t"
proof -
  have key: "s \<in> rel_dom Q" using member by (auto simp: rel_dom_def)
  have domain: "s \<in> rel_dom (schema_premises S)"
    using inst key by (simp add: schema_premise_instance_def)
  obtain e p where source: "(s,e,p) \<in> schema_premises S"
    using domain by (auto simp: rel_dom_def)
  obtain x where result: "(s,e,x) \<in> Q" "pattern_instance V p x"
    using inst source unfolding schema_premise_instance_def by blast
  have same: "d = e \<and> t = x"
    using inst member result(1) by (auto simp: schema_premise_instance_def single_valued_def)
  show ?thesis using source result same by blast
qed

lemma schema_instance_premise_iff:
  assumes inst: "schema_instance S V t Q"
  shows "(s,d,u) \<in> Q \<longleftrightarrow>
    (\<exists>p. (s,d,p) \<in> schema_premises S \<and> pattern_instance V p u)"
proof
  have body: "schema_premise_instance S V Q" using inst by (simp add: schema_instance_def)
  assume member: "(s,d,u) \<in> Q"
  show "\<exists>p. (s,d,p) \<in> schema_premises S \<and> pattern_instance V p u"
    by (rule schema_premise_instance_origin[OF body member])
next
  assume witness: "\<exists>p. (s,d,p) \<in> schema_premises S \<and> pattern_instance V p u"
  obtain p where source: "(s,d,p) \<in> schema_premises S" and pi: "pattern_instance V p u"
    using witness by blast
  have sv: "single_valued V" and body: "schema_premise_instance S V Q"
    using inst by (auto simp: schema_instance_def term_bindings_formed_def)
  obtain x where row: "(s,d,x) \<in> Q" and px: "pattern_instance V p x"
    using body source unfolding schema_premise_instance_def by blast
  have same: "u=x" by (rule pattern_instance_unique[OF sv pi px])
  show "(s,d,u) \<in> Q" using row same by simp
qed

lemma schema_premise_instance_unique:
  assumes sv: "single_valued V" and first: "schema_premise_instance S V Q"
    and second: "schema_premise_instance S V W"
  shows "Q = W"
proof -
  have compare: "\<And>A B. schema_premise_instance S V A \<Longrightarrow>
    schema_premise_instance S V B \<Longrightarrow> A \<subseteq> B"
  proof -
    fix A B assume a: "schema_premise_instance S V A" and b: "schema_premise_instance S V B"
    show "A \<subseteq> B"
    proof
      fix entry assume member: "entry \<in> A"
      obtain s d t where shape: "entry = (s,d,t)" by (cases entry) auto
      obtain p where source: "(s,d,p) \<in> schema_premises S" and inst: "pattern_instance V p t"
        using schema_premise_instance_origin[OF a] member shape by blast
      obtain x where result: "(s,d,x) \<in> B" "pattern_instance V p x"
        using b source unfolding schema_premise_instance_def by blast
      have "t = x" by (rule pattern_instance_unique[OF sv inst result(2)])
      then show "entry \<in> B" using shape result(1) by simp
    qed
  qed
  show ?thesis using compare[OF first second] compare[OF second first] by blast
qed

theorem schema_instance_unique:
  assumes "schema_instance S V t Q" "schema_instance S V u W"
  shows "t = u \<and> Q = W"
proof -
  have sv: "single_valued V" and first: "pattern_instance V (schema_conclusion S) t"
    and second: "pattern_instance V (schema_conclusion S) u"
    and q: "schema_premise_instance S V Q" and w: "schema_premise_instance S V W"
    using assms by (auto simp: schema_instance_def term_bindings_formed_def)
  show ?thesis using pattern_instance_unique[OF sv first second]
    schema_premise_instance_unique[OF sv q w] by blast
qed

lemma schema_premise_instance_exists:
  assumes formed: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
  shows "\<exists>Q. schema_premise_instance S V Q"
proof -
  let ?Q = "{(s,d,t). \<exists>p. (s,d,p) \<in> schema_premises S \<and> pattern_instance V p t}"
  have sv: "single_valued V" using bindings by (simp add: term_bindings_formed_def)
  have each: "\<And>s d p. (s,d,p) \<in> schema_premises S \<Longrightarrow> \<exists>t. pattern_instance V p t"
  proof -
    fix s d p assume member: "(s,d,p) \<in> schema_premises S"
    have pf: "pattern_formed p" using formed member by (auto simp: schema_formed_def)
    have used: "pattern_variables p \<subseteq> schema_variables S"
      using member by (auto simp: schema_variables_def)
    have scope: "pattern_variables p \<subseteq> rel_dom V"
      using used bindings by (simp add: term_bindings_formed_def)
    show "\<exists>t. pattern_instance V p t" by (rule pattern_instance_exists[OF pf scope])
  qed
  have domain: "rel_dom ?Q = rel_dom (schema_premises S)"
    using each by (auto simp: rel_dom_def; blast)
  have qsv: "single_valued ?Q"
  proof (unfold single_valued_def, intro allI impI)
    fix s y z assume first: "(s,y) \<in> ?Q" and second: "(s,z) \<in> ?Q"
    obtain d t where yp: "y = (d,t)" by (cases y) auto
    obtain e x where zp: "z = (e,x)" by (cases z) auto
    obtain p where left: "(s,d,p) \<in> schema_premises S" "pattern_instance V p t"
      using first yp by auto
    obtain q where right: "(s,e,q) \<in> schema_premises S" "pattern_instance V q x"
      using second zp by auto
    have same: "d = e \<and> p = q"
      using formed left(1) right(1) by (auto simp: schema_formed_def single_valued_def)
    have other: "pattern_instance V p x" using right(2) same by simp
    have terms: "t = x" by (rule pattern_instance_unique[OF sv left(2) other])
    show "y = z" using yp zp same terms by simp
  qed
  have finite_source: "finite (schema_premises S)" using formed by (simp add: schema_formed_def)
  have finite_domain: "finite (rel_dom ?Q)" using finite_rel_dom[OF finite_source] domain by simp
  have qfinite: "finite ?Q" by (rule finite_single_valued[OF finite_domain qsv])
  have result: "schema_premise_instance S V ?Q"
    using qfinite qsv domain each by (auto simp: schema_premise_instance_def; blast)
  show ?thesis using result by blast
qed

theorem schema_instance_exists:
  assumes formed: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
  shows "\<exists>t Q. schema_instance S V t Q"
proof -
  have pf: "pattern_formed (schema_conclusion S)" using formed by (simp add: schema_formed_def)
  have scope: "pattern_variables (schema_conclusion S) \<subseteq> rel_dom V"
    using bindings by (auto simp: term_bindings_formed_def schema_variables_def)
  obtain t where head: "pattern_instance V (schema_conclusion S) t"
    using pattern_instance_exists[OF pf scope] by blast
  obtain Q where body: "schema_premise_instance S V Q"
    using schema_premise_instance_exists[OF formed bindings] by blast
  show ?thesis using formed bindings head body unfolding schema_instance_def by blast
qed

lemma schema_instance_formed:
  assumes inst: "schema_instance S V t Q"
  shows "term_formed t \<and> (\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> term_formed x)"
proof -
  have bindings: "term_bindings_formed (schema_variables S) V"
    and head: "pattern_instance V (schema_conclusion S) t"
    and body: "schema_premise_instance S V Q" using inst by (auto simp: schema_instance_def)
  have head_formed: "term_formed t" by (rule pattern_instance_formed_term[OF bindings head])
  have premises_formed: "\<forall>s d x. (s,d,x) \<in> Q \<longrightarrow> term_formed x"
    using schema_premise_instance_origin[OF body] pattern_instance_formed_term[OF bindings] by blast
  show ?thesis using head_formed premises_formed by blast
qed

lemma schema_instance_socket_boundary:
  assumes "schema_instance S V t Q"
  shows "finite Q \<and> single_valued Q \<and> rel_dom Q = rel_dom (schema_premises S)"
  using assms by (simp add: schema_instance_def schema_premise_instance_def)

lemma schema_instance_missing_socket_rejected:
  assumes "s \<in> rel_dom (schema_premises S)" "s \<notin> rel_dom Q"
  shows "\<not> schema_instance S V t Q"
  using assms schema_instance_socket_boundary by blast

lemma schema_instance_extra_socket_rejected:
  assumes "s \<notin> rel_dom (schema_premises S)" "s \<in> rel_dom Q"
  shows "\<not> schema_instance S V t Q"
  using assms schema_instance_socket_boundary by blast

lemma schema_instance_target_boundary:
  assumes "schema_instance S V t Q"
  shows "fst ` rel_ran Q = schema_dependencies S"
proof -
  have body: "schema_premise_instance S V Q" using assms by (simp add: schema_instance_def)
  have targets: "\<And>M :: ('s \<times> ('d \<times> 'v)) set. \<And>d.
    d \<in> fst ` rel_ran M \<longleftrightarrow> (\<exists>s x. (s,d,x) \<in> M)"
    by (auto simp: rel_ran_def intro: rev_image_eqI; blast)
  show ?thesis using body schema_premise_instance_origin[OF body]
    by (auto simp: set_eq_iff schema_dependencies_def schema_premise_instance_def targets; blast)
qed

lemma schema_material_instance_boundary:
  assumes schema: "schema_instance S V t Q" and member: "(s,M) \<in> schema_material_premises S"
  shows "\<exists>x a e b f. material_pattern_instance V M x a e b f \<and>
    term_formed x \<and> term_formed a \<and> term_formed e \<and> term_formed b \<and> term_formed f"
proof -
  have sf: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) V"
    using schema by (auto simp: schema_instance_def)
  have mf: "material_pattern_formed M" using sf member by (auto simp: schema_formed_def)
  have used: "material_variables M \<subseteq> schema_variables S"
    using member by (auto simp: schema_variables_def)
  have scope: "material_variables M \<subseteq> rel_dom V"
    using used bindings by (simp add: term_bindings_formed_def)
  obtain x a e b f where inst: "material_pattern_instance V M x a e b f"
    using material_pattern_instance_exists[OF mf scope] by blast
  show ?thesis using inst material_pattern_instance_formed[OF bindings inst] by blast
qed

text \<open>
  The schema stores a conclusion pattern and a complete finite graph from
  call sockets to prospective calls and material sockets to complete material
  patterns. Their domains are disjoint. Variable scope is derived from every
  field; direct semantic dependencies are the prospective callees. Instantiation
  preserves every socket, including distinct sockets carrying equal calls or
  equal material patterns. Every material socket has one formed operand tuple
  under the same complete binding assignment. No truth or proof field is stored.

  These are mathematical projections. Native presentation recovery and the
  positive meaning construction are separate relations built from them.
\<close>

end
