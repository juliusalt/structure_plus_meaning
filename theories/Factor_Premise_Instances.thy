theory Factor_Premise_Instances
  imports Factor_Binding_Admission
begin

section \<open>Complete socket projections under one substitution\<close>

definition call_instance_relation ::
  "('a \<times> factor_term) set \<Rightarrow> ('s \<times> ('d \<times> 'a term_pattern)) set \<Rightarrow>
    ('s \<times> ('d \<times> factor_term)) set" where
  "call_instance_relation B A = {(s,d,t). \<exists>p. (s,d,p)\<in>A \<and> pattern_instance B p t}"

definition material_instance_relation ::
  "('a \<times> factor_term) set \<Rightarrow> ('s \<times> 'a material_pattern) set \<Rightarrow>
    ('s \<times> factor_term) set" where
  "material_instance_relation B A = {(q,t). \<exists>M s a e b f. (q,M)\<in>A \<and>
    t=material_tuple s a e b f \<and> material_pattern_instance B M s a e b f}"

definition premise_family_variables ::
  "('s \<times> ('d \<times> 'a term_pattern)) set \<Rightarrow> ('s \<times> 'a material_pattern) set \<Rightarrow> 'a set" where
  "premise_family_variables A C =
    (\<Union>(s,d,p)\<in>A. pattern_variables p) \<union> (\<Union>(s,M)\<in>C. material_variables M)"

lemma call_instance_relation_insert:
  assumes "single_valued B" "pattern_instance B p t"
  shows "call_instance_relation B (insert (s,d,p) A)=insert (s,d,t) (call_instance_relation B A)"
proof -
  have inst_iff: "pattern_instance B p x \<longleftrightarrow> x=t" for x
  proof
    assume other: "pattern_instance B p x"
    show "x=t" by (rule pattern_instance_unique[OF assms(1) other assms(2)])
  next
    assume "x=t"
    then show "pattern_instance B p x" using assms(2) by simp
  qed
  show ?thesis by (auto simp: call_instance_relation_def inst_iff)
qed

lemma material_instance_relation_insert:
  assumes "single_valued B" "material_pattern_instance B M s a e b f"
  shows "material_instance_relation B (insert (q,M) A)=
    insert (q,material_tuple s a e b f) (material_instance_relation B A)"
proof -
  have inst_iff: "material_pattern_instance B M x y z w v \<longleftrightarrow>
    x=s \<and> y=a \<and> z=e \<and> w=b \<and> v=f" for x y z w v
  proof
    assume other: "material_pattern_instance B M x y z w v"
    have "(x,y,z,w,v)=(s,a,e,b,f)" by (rule material_pattern_instance_unique[OF assms(1) other assms(2)])
    then show "x=s \<and> y=a \<and> z=e \<and> w=b \<and> v=f" by simp
  next
    assume "x=s \<and> y=a \<and> z=e \<and> w=b \<and> v=f"
    then show "material_pattern_instance B M x y z w v" using assms(2) by simp
  qed
  show ?thesis by (auto simp: material_instance_relation_def inst_iff; blast)
qed

lemma call_instance_relation_boundary:
  assumes finite: "finite A" and source: "single_valued A" and single: "single_valued B"
    and instances: "\<forall>s d p. (s,d,p)\<in>A \<longrightarrow> (\<exists>t. pattern_instance B p t)"
  shows "finite (call_instance_relation B A) \<and> single_valued (call_instance_relation B A) \<and>
    rel_dom (call_instance_relation B A)=rel_dom A"
proof -
  have domain: "rel_dom (call_instance_relation B A)=rel_dom A"
    using instances by (auto simp: call_instance_relation_def rel_dom_def; blast)
  have sv: "single_valued (call_instance_relation B A)"
  proof (unfold single_valued_def, intro allI impI)
    fix s x y assume left: "(s,x)\<in>call_instance_relation B A"
      and right: "(s,y)\<in>call_instance_relation B A"
    obtain d p t where first: "x=(d,t)" "(s,d,p)\<in>A" "pattern_instance B p t"
      using left by (auto simp: call_instance_relation_def)
    obtain e q v where second: "y=(e,v)" "(s,e,q)\<in>A" "pattern_instance B q v"
      using right by (auto simp: call_instance_relation_def)
    have same: "d=e" "p=q" using single_valued_outputs[OF source first(2) second(2)] by auto
    have terms: "t=v" using pattern_instance_unique[OF single first(3)] second(3) same by blast
    show "x=y" using first(1) second(1) same terms by simp
  qed
  have fin: "finite (call_instance_relation B A)"
    by (rule finite_single_valued[OF _ sv]) (simp add: domain finite_rel_dom[OF finite])
  show ?thesis using fin sv domain by blast
qed

lemma material_instance_relation_boundary:
  assumes finite: "finite A" and source: "single_valued A" and single: "single_valued B"
    and instances: "\<forall>q M. (q,M)\<in>A \<longrightarrow> (\<exists>s a e b f. material_pattern_instance B M s a e b f)"
  shows "finite (material_instance_relation B A) \<and> single_valued (material_instance_relation B A) \<and>
    rel_dom (material_instance_relation B A)=rel_dom A"
proof -
  have domain: "rel_dom (material_instance_relation B A)=rel_dom A"
  proof (rule set_eqI)
    fix q
    show "q\<in>rel_dom (material_instance_relation B A) \<longleftrightarrow> q\<in>rel_dom A"
    proof
      assume "q\<in>rel_dom (material_instance_relation B A)"
      then obtain t where row: "(q,t)\<in>material_instance_relation B A" by (auto simp: rel_dom_def)
      obtain M where "(q,M)\<in>A" using row by (auto simp: material_instance_relation_def)
      then show "q\<in>rel_dom A" by blast
    next
      assume "q\<in>rel_dom A"
      then obtain M where member: "(q,M)\<in>A" by (auto simp: rel_dom_def)
      obtain s a e b f where inst: "material_pattern_instance B M s a e b f" using instances member by blast
      have row: "(q,material_tuple s a e b f)\<in>material_instance_relation B A"
        using member inst by (auto simp: material_instance_relation_def; blast)
      show "q\<in>rel_dom (material_instance_relation B A)" using row by blast
    qed
  qed
  have sv: "single_valued (material_instance_relation B A)"
  proof (unfold single_valued_def, intro allI impI)
    fix q x y assume left: "(q,x)\<in>material_instance_relation B A"
      and right: "(q,y)\<in>material_instance_relation B A"
    obtain M s a e b f where first: "(q,M)\<in>A" "x=material_tuple s a e b f"
      "material_pattern_instance B M s a e b f" using left by (auto simp: material_instance_relation_def)
    obtain N s' a' e' b' f' where second: "(q,N)\<in>A" "y=material_tuple s' a' e' b' f'"
      "material_pattern_instance B N s' a' e' b' f'" using right by (auto simp: material_instance_relation_def)
    have same: "M=N" by (rule single_valued_outputs[OF source first(1) second(1)])
    have terms: "(s,a,e,b,f)=(s',a',e',b',f')"
      using material_pattern_instance_unique[OF single first(3)] second(3) same by blast
    show "x=y" using first(2) second(2) terms by (auto simp: material_tuple_def)
  qed
  have fin: "finite (material_instance_relation B A)"
    by (rule finite_single_valued[OF _ sv]) (simp add: domain finite_rel_dom[OF finite])
  show ?thesis using fin sv domain by blast
qed

lemma schema_premise_instance_relation:
  fixes S :: "('a,'s,'d) factor_schema"
  assumes "single_valued B" "schema_premise_instance S B Q"
  shows "Q=call_instance_relation B (schema_premises S)"
proof (rule set_eqI)
  fix row :: "'s \<times> ('d \<times> factor_term)"
  obtain s d t where shape: "row=(s,d,t)" by (cases row) auto
  have reverse: "(s,d,p)\<in>schema_premises S \<Longrightarrow> pattern_instance B p t \<Longrightarrow> (s,d,t)\<in>Q" for p
  proof -
    assume source: "(s,d,p)\<in>schema_premises S" and inst: "pattern_instance B p t"
    obtain x where found: "(s,d,x)\<in>Q" "pattern_instance B p x"
      using assms(2) source unfolding schema_premise_instance_def by blast
    have "t=x" by (rule pattern_instance_unique[OF assms(1) inst found(2)])
    then show "(s,d,t)\<in>Q" using found(1) by simp
  qed
  show "row\<in>Q \<longleftrightarrow> row\<in>call_instance_relation B (schema_premises S)"
    using schema_premise_instance_origin[OF assms(2)] reverse
    by (auto simp: shape call_instance_relation_def)
qed

theorem schema_premise_instance_relation_iff:
  assumes formed: "schema_formed S" and bindings: "term_bindings_formed (schema_variables S) B"
  shows "schema_premise_instance S B Q \<longleftrightarrow> Q=call_instance_relation B (schema_premises S)"
proof -
  have single: "single_valued B" using bindings by (simp add: term_bindings_formed_def)
  obtain W where inst: "schema_premise_instance S B W"
    using schema_premise_instance_exists[OF formed bindings] by blast
  show ?thesis using schema_premise_instance_relation[OF single] inst by blast
qed

lemma native_family_instance_boundaries:
  assumes family: "native_premise_family_at E u V r A C" and bindings: "term_bindings_formed V B"
  shows "finite (call_instance_relation B A) \<and> single_valued (call_instance_relation B A) \<and>
    rel_dom (call_instance_relation B A)=rel_dom A \<and>
    finite (material_instance_relation B C) \<and> single_valued (material_instance_relation B C) \<and>
    rel_dom (material_instance_relation B C)=rel_dom C"
proof -
  have source: "finite A" "single_valued A" "finite C" "single_valued C"
    "\<forall>s d p. (s,d,p)\<in>A \<longrightarrow> pattern_formed p \<and> pattern_variables p\<subseteq>V"
    "\<forall>s M. (s,M)\<in>C \<longrightarrow> material_pattern_formed M \<and> material_variables M\<subseteq>V"
    using native_premise_family_formed[OF family] by auto
  have single: "single_valued B" and domain: "rel_dom B=V"
    using bindings by (auto simp: term_bindings_formed_def)
  have calls: "\<forall>s d p. (s,d,p)\<in>A \<longrightarrow> (\<exists>t. pattern_instance B p t)"
    using source(5) domain pattern_instance_exists by blast
  have materials: "\<forall>s M. (s,M)\<in>C \<longrightarrow> (\<exists>x a e b f. material_pattern_instance B M x a e b f)"
    using source(6) domain material_pattern_instance_exists by blast
  show ?thesis using call_instance_relation_boundary[OF source(1,2) single calls]
    material_instance_relation_boundary[OF source(3,4) single materials] by blast
qed

section \<open>Ordered rows retain every source socket before the family order is forgotten\<close>

inductive instantiated_premise_rows ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> (local_address \<times> factor_term) set \<Rightarrow>
    (local_address \<times> local_address) list \<Rightarrow>
    (local_address \<times> ('u definition_site \<times> factor_term)) list \<Rightarrow>
    (local_address \<times> factor_term) list \<Rightarrow> local_address set \<Rightarrow> bool"
  for E u V B where
  empty: "instantiated_premise_rows E u V B [] [] [] {}"
| call: "prospective_call_at E u V r d p I K \<Longrightarrow> pattern_instance B p t \<Longrightarrow>
    instantiated_premise_rows E u V B rs qs cs U \<Longrightarrow>
    instantiated_premise_rows E u V B ((s,r)#rs) ((s,d,t)#qs) cs (pattern_variables p\<union>U)"
| material: "native_material_at E u V r M I K \<Longrightarrow> material_pattern_instance B M x a e b f \<Longrightarrow>
    instantiated_premise_rows E u V B rs qs cs U \<Longrightarrow>
    instantiated_premise_rows E u V B ((s,r)#rs) qs ((s,material_tuple x a e b f)#cs) (material_variables M\<union>U)"

lemma instantiated_premise_row_keys:
  assumes "instantiated_premise_rows E u V B rs qs cs U"
  shows "mset (map fst rs)=mset (map fst qs)+mset (map fst cs)"
  using assms by (induction rule: instantiated_premise_rows.induct) (simp_all add: add.assoc add.left_commute)

lemma instantiated_premise_row_variables:
  assumes "instantiated_premise_rows E u V B rs qs cs U"
  shows "finite U \<and> U\<subseteq>V"
  using assms by (induction rule: instantiated_premise_rows.induct)
    (auto dest: prospective_call_formed native_material_formed)

lemma instantiated_premise_rows_append:
  assumes "instantiated_premise_rows E u V B rs qs cs U"
    "instantiated_premise_rows E u V B ts ws ds W"
  shows "instantiated_premise_rows E u V B (rs@ts) (qs@ws) (cs@ds) (U\<union>W)"
  using assms(1) by (induction rule: instantiated_premise_rows.induct)
    (use assms(2) in \<open>auto simp: Un_assoc intro: instantiated_premise_rows.intros\<close>)

lemma instantiated_premise_rows_contents:
  assumes read: "instantiated_premise_rows E u V B rs qs cs U"
    and single: "single_valued B" and keys: "distinct (map fst rs)"
  shows "\<exists>A C. finite A \<and> finite C \<and> single_valued (socket_sum A C) \<and>
    rel_dom (socket_sum A C)=rel_dom (set rs) \<and>
    (\<forall>s a. (s,a)\<in>set rs \<longrightarrow> (\<exists>p I K. (s,p)\<in>socket_sum A C \<and> native_premise_at E u V a p I K)) \<and>
    set qs=call_instance_relation B A \<and> set cs=material_instance_relation B C \<and>
    U=premise_family_variables A C"
  using read keys
proof (induction rule: instantiated_premise_rows.induct)
  case empty
  show ?case by (rule exI[of _ "{}"], rule exI[of _ "{}"])
    (simp add: socket_sum_def single_valued_def call_instance_relation_def
      material_instance_relation_def premise_family_variables_def rel_dom_def)
next
  case (call r d p I K t rs qs cs U s)
  have tail_keys: "distinct (map fst rs)" and fresh: "s\<notin>set (map fst rs)" using call.prems by auto
  obtain A C where tail: "finite A" "finite C" "single_valued (socket_sum A C)"
    "rel_dom (socket_sum A C)=rel_dom (set rs)"
    "\<forall>s a. (s,a)\<in>set rs \<longrightarrow> (\<exists>p I K. (s,p)\<in>socket_sum A C \<and> native_premise_at E u V a p I K)"
    "set qs=call_instance_relation B A" "set cs=material_instance_relation B C"
    "U=premise_family_variables A C" using call.IH[OF tail_keys] by blast
  have domains: "rel_dom A\<union>rel_dom C=set (map fst rs)"
    using tail(4)[unfolded socket_sum_domain] by (simp only: rel_dom_image set_map)
  have absent: "s\<notin>rel_dom A" "s\<notin>rel_dom C" using fresh domains by auto
  have sv: "single_valued (socket_sum (insert (s,d,p) A) C)"
    using tail(3) absent by (simp only: socket_sum_single_valued; auto simp: single_valued_def rel_dom_def; blast)
  have domain: "rel_dom (socket_sum (insert (s,d,p) A) C)=rel_dom (set ((s,r)#rs))"
    using tail(4)[unfolded socket_sum_domain] by (simp only: socket_sum_domain; simp add: rel_dom_image)
  have head: "native_premise_at E u V r (Inl (d,p)) I K" using call.hyps(1) by simp
  have body: "\<forall>q a. (q,a)\<in>set ((s,r)#rs) \<longrightarrow>
    (\<exists>v I K. (q,v)\<in>socket_sum (insert (s,d,p) A) C \<and> native_premise_at E u V a v I K)"
    using tail(5) head by (auto simp: socket_sum_def; blast)
  show ?case by (rule exI[of _ "insert (s,d,p) A"], rule exI[of _ C])
    (use tail sv body domain call_instance_relation_insert[OF single call.hyps(2), of s d A]
      in \<open>auto simp: premise_family_variables_def\<close>)
next
  case (material r M I K x a e b f rs qs cs U s)
  have tail_keys: "distinct (map fst rs)" and fresh: "s\<notin>set (map fst rs)" using material.prems by auto
  obtain A C where tail: "finite A" "finite C" "single_valued (socket_sum A C)"
    "rel_dom (socket_sum A C)=rel_dom (set rs)"
    "\<forall>s a. (s,a)\<in>set rs \<longrightarrow> (\<exists>p I K. (s,p)\<in>socket_sum A C \<and> native_premise_at E u V a p I K)"
    "set qs=call_instance_relation B A" "set cs=material_instance_relation B C"
    "U=premise_family_variables A C" using material.IH[OF tail_keys] by blast
  have domains: "rel_dom A\<union>rel_dom C=set (map fst rs)"
    using tail(4)[unfolded socket_sum_domain] by (simp only: rel_dom_image set_map)
  have absent: "s\<notin>rel_dom A" "s\<notin>rel_dom C" using fresh domains by auto
  have sv: "single_valued (socket_sum A (insert (s,M) C))"
    using tail(3) absent by (simp only: socket_sum_single_valued; auto simp: single_valued_def rel_dom_def; blast)
  have domain: "rel_dom (socket_sum A (insert (s,M) C))=rel_dom (set ((s,r)#rs))"
    using tail(4)[unfolded socket_sum_domain] by (simp only: socket_sum_domain; simp add: rel_dom_image)
  have head: "native_premise_at E u V r (Inr M) I K" using material.hyps(1) by simp
  have body: "\<forall>q a. (q,a)\<in>set ((s,r)#rs) \<longrightarrow>
    (\<exists>v I K. (q,v)\<in>socket_sum A (insert (s,M) C) \<and> native_premise_at E u V a v I K)"
    using tail(5) head by (auto simp: socket_sum_def; blast)
  show ?case by (rule exI[of _ A], rule exI[of _ "insert (s,M) C"])
    (use tail sv body domain material_instance_relation_insert[OF single material.hyps(2), of s C]
      in \<open>auto simp: premise_family_variables_def\<close>)
qed

lemma instantiated_premise_rows_family:
  assumes environment: "environment_formed E" and source: "artifact_at E u R"
    and family: "family_at R r (set rs)" and order: "distinct rs"
    and bindings: "single_valued B" and read: "instantiated_premise_rows E u V B rs qs cs U"
  shows "\<exists>A C. native_premise_family_at E u V r A C \<and>
    set qs=call_instance_relation B A \<and> set cs=material_instance_relation B C \<and>
    U=premise_family_variables A C"
proof -
  have keys: "distinct (map fst rs)" using order family
    by (simp add: distinct_keys_iff family_at_def)
  obtain A C where parts: "finite A" "finite C" "single_valued (socket_sum A C)"
    "rel_dom (socket_sum A C)=rel_dom (set rs)"
    "\<forall>s a. (s,a)\<in>set rs \<longrightarrow> (\<exists>p I K. (s,p)\<in>socket_sum A C \<and> native_premise_at E u V a p I K)"
    "set qs=call_instance_relation B A" "set cs=material_instance_relation B C"
    "U=premise_family_variables A C"
    using instantiated_premise_rows_contents[OF read bindings keys] by blast
  have native: "native_premise_family_at E u V r A C"
    unfolding native_premise_family_at_def
    by (rule conjI[OF environment], rule exI[of _ R], rule exI[of _ "set rs"])
      (use source family parts(1-5) in auto)
  show ?thesis using native parts(6-8) by blast
qed

lemma instantiated_premise_rows_distinct:
  assumes read: "instantiated_premise_rows E u V B rs qs cs U" and keys: "distinct (map fst rs)"
  shows "distinct qs \<and> distinct cs \<and> rel_dom (set qs)\<inter>rel_dom (set cs)={}"
proof -
  have same: "mset (map fst rs)=mset (map fst qs@map fst cs)"
    using instantiated_premise_row_keys[OF read] by simp
  have all: "distinct (map fst qs@map fst cs)" using mset_eq_imp_distinct_iff[OF same] keys by blast
  show ?thesis using all by (auto simp: distinct_append distinct_keys_iff rel_dom_image)
qed

lemma instantiated_call_rows_exists:
  assumes each: "\<forall>s d t. (s,d,t)\<in>set qs \<longrightarrow>
    (\<exists>p I K. prospective_call_at E u V (f s) d p I K \<and> pattern_instance B p t)"
  shows "\<exists>U. instantiated_premise_rows E u V B (map (\<lambda>(s,d,t). (s,f s)) qs) qs [] U"
  using each
proof (induction qs)
  case Nil
  show ?case by (rule exI[of _ "{}"]) (simp add: instantiated_premise_rows.empty)
next
  case (Cons row qs)
  obtain s d t where shape: "row=(s,d,t)" by (cases row) auto
  have member: "(s,d,t)\<in>set (row#qs)" by (simp add: shape)
  obtain p I K where head: "prospective_call_at E u V (f s) d p I K" "pattern_instance B p t"
    using Cons.prems[rule_format, OF member] by blast
  have tail_each: "\<forall>s d t. (s,d,t)\<in>set qs \<longrightarrow>
    (\<exists>p I K. prospective_call_at E u V (f s) d p I K \<and> pattern_instance B p t)"
    by (intro allI impI; rule Cons.prems[rule_format]; simp)
  obtain U where tail: "instantiated_premise_rows E u V B (map (\<lambda>(s,d,t). (s,f s)) qs) qs [] U"
    using Cons.IH[OF tail_each] by blast
  show ?case by (rule exI[of _ "pattern_variables p\<union>U"])
    (use instantiated_premise_rows.call[OF head tail, of s] in \<open>simp add: shape split_def\<close>)
qed

lemma instantiated_material_rows_exists:
  assumes each: "\<forall>s t. (s,t)\<in>set cs \<longrightarrow>
    (\<exists>M I K x a e b g. native_material_at E u V (f s) M I K \<and>
      material_pattern_instance B M x a e b g \<and> t=material_tuple x a e b g)"
  shows "\<exists>U. instantiated_premise_rows E u V B (map (\<lambda>(s,t). (s,f s)) cs) [] cs U"
  using each
proof (induction cs)
  case Nil
  show ?case by (rule exI[of _ "{}"]) (simp add: instantiated_premise_rows.empty)
next
  case (Cons row cs)
  obtain s t where shape: "row=(s,t)" by (cases row)
  have member: "(s,t)\<in>set (row#cs)" by (simp add: shape)
  obtain M I K x a e b g where head: "native_material_at E u V (f s) M I K"
    "material_pattern_instance B M x a e b g" "t=material_tuple x a e b g"
    using Cons.prems[rule_format, OF member] by blast
  have tail_each: "\<forall>s t. (s,t)\<in>set cs \<longrightarrow>
    (\<exists>M I K x a e b g. native_material_at E u V (f s) M I K \<and>
      material_pattern_instance B M x a e b g \<and> t=material_tuple x a e b g)"
    by (intro allI impI; rule Cons.prems[rule_format]; simp)
  obtain U where tail: "instantiated_premise_rows E u V B (map (\<lambda>(s,t). (s,f s)) cs) [] cs U"
    using Cons.IH[OF tail_each] by blast
  show ?case by (rule exI[of _ "material_variables M\<union>U"])
    (use instantiated_premise_rows.material[OF head(1,2) tail, of s] in \<open>simp add: shape head(3) split_def\<close>)
qed

theorem native_family_instantiated_rows:
  assumes family: "native_premise_family_at E u V r A C" and bindings: "term_bindings_formed V B"
    and calls: "set qs=call_instance_relation B A" and materials: "set cs=material_instance_relation B C"
    and order: "distinct qs" "distinct cs"
  shows "\<exists>R rs. artifact_at E u R \<and> family_at R r (set rs) \<and> distinct rs \<and>
    instantiated_premise_rows E u V B rs qs cs (premise_family_variables A C)"
proof -
  obtain R M where source: "environment_formed E" "artifact_at E u R" "family_at R r M"
    "single_valued (socket_sum A C)" "rel_dom (socket_sum A C)=rel_dom M"
    "\<forall>s a. (s,a)\<in>M \<longrightarrow>
      (\<exists>p. (s,p)\<in>socket_sum A C \<and> (\<exists>I K. native_premise_at E u V a p I K))"
    using family by (auto simp: native_premise_family_at_def)
  have functional: "single_valued M" using source(3) by (simp add: family_at_def)
  have origin: "(s,p)\<in>socket_sum A C \<Longrightarrow>
    \<exists>a I K. (s,a)\<in>M \<and> native_premise_at E u V a p I K" for s p
    using complete_socket_reading_origin[OF source(4-6)] by blast
  let ?f="rel_value M"
  have call_reads: "\<forall>s d t. (s,d,t)\<in>set qs \<longrightarrow>
    (\<exists>p I K. prospective_call_at E u V (?f s) d p I K \<and> pattern_instance B p t)"
  proof (intro allI impI)
    fix s d t assume member: "(s,d,t)\<in>set qs"
    obtain p where head: "(s,d,p)\<in>A" "pattern_instance B p t"
      using member calls by (auto simp: call_instance_relation_def)
    have in_sum: "(s,Inl (d,p))\<in>socket_sum A C" using head(1) by simp
    obtain a I K where read: "(s,a)\<in>M" "prospective_call_at E u V a d p I K"
      using origin[OF in_sum] by auto
    have selected: "?f s=a" by (rule rel_value_eq[OF functional read(1)])
    show "\<exists>p I K. prospective_call_at E u V (?f s) d p I K \<and> pattern_instance B p t"
      using read(2) selected head(2) by blast
  qed
  have material_reads: "\<forall>s t. (s,t)\<in>set cs \<longrightarrow>
    (\<exists>N I K x a e b g. native_material_at E u V (?f s) N I K \<and>
      material_pattern_instance B N x a e b g \<and> t=material_tuple x a e b g)"
  proof (intro allI impI)
    fix s t assume member: "(s,t)\<in>set cs"
    obtain N x a e b g where head: "(s,N)\<in>C" "t=material_tuple x a e b g"
      "material_pattern_instance B N x a e b g" using member materials
      by (auto simp: material_instance_relation_def)
    have in_sum: "(s,Inr N)\<in>socket_sum A C" using head(1) by simp
    obtain root I K where read: "(s,root)\<in>M" "native_material_at E u V root N I K"
      using origin[OF in_sum] by auto
    have selected: "?f s=root" by (rule rel_value_eq[OF functional read(1)])
    show "\<exists>N I K x a e b g. native_material_at E u V (?f s) N I K \<and>
      material_pattern_instance B N x a e b g \<and> t=material_tuple x a e b g"
      using read(2) selected head(2,3) by blast
  qed
  let ?left="map (\<lambda>(s,d,t). (s,?f s)) qs"
  let ?right="map (\<lambda>(s,t). (s,?f s)) cs"
  let ?rs="?left@?right"
  obtain U where left: "instantiated_premise_rows E u V B ?left qs [] U"
    using instantiated_call_rows_exists[OF call_reads] by blast
  obtain W where right: "instantiated_premise_rows E u V B ?right [] cs W"
    using instantiated_material_rows_exists[OF material_reads] by blast
  have read: "instantiated_premise_rows E u V B ?rs qs cs (U\<union>W)"
    using instantiated_premise_rows_append[OF left right] by simp
  have bounds: "single_valued (set qs)" "rel_dom (set qs)=rel_dom A"
    "single_valued (set cs)" "rel_dom (set cs)=rel_dom C"
    using native_family_instance_boundaries[OF family bindings] calls materials by auto
  have key_set: "set (map fst qs@map fst cs)=rel_dom M"
    using source(5)[unfolded socket_sum_domain]
    by (simp only: set_append set_map rel_dom_image[symmetric] bounds(2,4))
  have disjoint: "rel_dom A\<inter>rel_dom C={}" using source(4) by (simp add: socket_sum_single_valued)
  have call_keys: "distinct (map fst qs)" using order(1) bounds(1) by (simp only: distinct_keys_iff)
  have material_keys: "distinct (map fst cs)" using order(2) bounds(3) by (simp only: distinct_keys_iff)
  have separated: "set (map fst qs)\<inter>set (map fst cs)={}"
    by (simp only: set_map rel_dom_image[symmetric] bounds(2,4)) (rule disjoint)
  have keys: "distinct (map fst qs@map fst cs)" using call_keys material_keys separated by simp
  have row_shape: "?rs=map (\<lambda>s. (s,?f s)) (map fst qs@map fst cs)"
    by (simp add: comp_def split_def)
  have "set ?rs=image (\<lambda>s. (s,?f s)) (rel_dom M)"
    using arg_cong[OF row_shape, where f=set] by (simp only: set_map key_set)
  also have "...=graph_map (rel_dom M) ?f" by (auto simp: graph_map_def)
  also have "...=M" by (rule sym[OF single_valued_graph[OF functional]])
  finally have rows: "set ?rs=M" .
  have mapped_distinct: "distinct (map (\<lambda>s. (s,?f s)) (map fst qs@map fst cs))"
    using keys by (simp only: distinct_map; auto simp: inj_on_def)
  have separate: "distinct ?rs"
    using arg_cong[OF row_shape, where f=distinct] mapped_distinct by blast
  have actual: "family_at R r (set ?rs)" using source(3) rows by simp
  have single: "single_valued B" using bindings by (simp add: term_bindings_formed_def)
  obtain D F where recovered: "native_premise_family_at E u V r D F"
    "U\<union>W=premise_family_variables D F"
    using instantiated_premise_rows_family[OF source(1,2) actual separate single read] by blast
  have same: "D=A" "F=C" using native_premise_family_unique[OF recovered(1) family] by auto
  show ?thesis by (rule exI[of _ R], rule exI[of _ ?rs])
    (use source(2) actual separate read recovered(2) same in auto)
qed

section \<open>Faithful ordinary values for the instantiated calls\<close>

definition call_instance_value ::
  "local_address option definition_site \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "call_instance_value d t=Pair_Term (site_data_term (fst d) (snd d)) t"

lemma call_instance_value_injective:
  "call_instance_value d t=call_instance_value e x \<longleftrightarrow> d=e \<and> t=x"
  by (cases d; cases e) (simp add: call_instance_value_def)

abbreviation call_instance_rows_term ::
  "(local_address \<times> (local_address option definition_site \<times> factor_term)) list \<Rightarrow> factor_term" where
  "call_instance_rows_term qs \<equiv> binding_rows_term (map (\<lambda>(s,d,t). (s,call_instance_value d t)) qs)"

lemma call_instance_rows_map_injective:
  "map (\<lambda>(s,d,t). (s,call_instance_value d t)) qs=
    map (\<lambda>(s,d,t). (s,call_instance_value d t)) cs \<longleftrightarrow> qs=cs"
proof -
  have injective: "inj (\<lambda>(s,d,t). (s,call_instance_value d t))"
    by (rule injI; rename_tac x y; case_tac x; case_tac y)
      (auto simp: call_instance_value_injective split: prod.splits)
  show ?thesis by (rule injective_mapped_lists[OF injective])
qed

lemma call_instance_rows_term_injective:
  "call_instance_rows_term qs=call_instance_rows_term cs \<longleftrightarrow> qs=cs"
  by (simp only: binding_rows_term_injective call_instance_rows_map_injective)

text \<open>
  The two finite instance relations retain the original socket as the row key.
  Their domains are exactly the source call and material domains whenever the
  complete bindings are formed. The call projection is the existing schema
  premise instance; the material projection contains the five actual operands
  in the existing tuple and makes no material-observation assertion.

  Ordered row traversal retains the order within each output part. Every
  independent pair of complete distinct output orders has a corresponding
  source-row enumeration of the same actual family. This also covers empty
  families and distinct sockets with identical endpoints or instances.
  The family grammar supplies no separation of different premise interiors,
  and no such condition is introduced here.
\<close>

end
