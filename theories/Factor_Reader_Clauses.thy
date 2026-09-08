theory Factor_Reader_Clauses
  imports Factor_Data_Comparison Factor_Pattern_Programs
begin

section \<open>An ordinary premise either supplies a result or matches a fixed one\<close>

definition reader_projection_clause ::
  "'a \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> ('a,'s,'d) factor_schema" where
  "reader_projection_clause x y s reader =
    data_rule (Pattern_Variable x) {(s,reader,Pattern_Pair (Pattern_Variable x) (Pattern_Variable y))}"

definition fixed_result_clause ::
  "'a \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> factor_term \<Rightarrow> ('a,'s,'d) factor_schema" where
  "fixed_result_clause x s reader v =
    data_rule (Pattern_Variable x) {(s,reader,Pattern_Pair (Pattern_Variable x) (exact_term_pattern v))}"

lemma reader_projection_clause_formed [simp]:
  "schema_formed (reader_projection_clause x y s reader)"
  by (simp add: reader_projection_clause_def schema_formed_def single_valued_def)

lemma reader_projection_clause_variables [simp]:
  "schema_variables (reader_projection_clause x y s reader)={x,y}"
  by (auto simp: reader_projection_clause_def schema_variables_def)

lemma reader_projection_clause_dependencies [simp]:
  "schema_dependencies (reader_projection_clause x y s reader)={reader}"
  by (auto simp: reader_projection_clause_def schema_dependencies_def rel_ran_def)

lemma reader_projection_clause_sockets [simp]:
  "schema_sockets (reader_projection_clause x y s reader)={s}"
  by (auto simp: reader_projection_clause_def schema_sockets_def rel_dom_def)

lemma reader_projection_clause_ordinary [simp]:
  "schema_material_premises (reader_projection_clause x y s reader)={}"
  by (simp add: reader_projection_clause_def)

lemma fixed_result_clause_formed [simp]:
  "schema_formed (fixed_result_clause x s reader v) \<longleftrightarrow> term_formed v"
  by (simp add: fixed_result_clause_def schema_formed_def single_valued_def)

lemma fixed_result_clause_variables [simp]:
  "schema_variables (fixed_result_clause x s reader v)={x}"
  by (simp add: fixed_result_clause_def schema_variables_def)

lemma fixed_result_clause_dependencies [simp]:
  "schema_dependencies (fixed_result_clause x s reader v)={reader}"
  by (auto simp: fixed_result_clause_def schema_dependencies_def rel_ran_def)

lemma fixed_result_clause_sockets [simp]:
  "schema_sockets (fixed_result_clause x s reader v)={s}"
  by (auto simp: fixed_result_clause_def schema_sockets_def rel_dom_def)

lemma fixed_result_clause_ordinary [simp]:
  "schema_material_premises (fixed_result_clause x s reader v)={}"
  by (simp add: fixed_result_clause_def)

lemma rename_reader_projection_clause [simp]:
  "rename_schema f h g (reader_projection_clause x y s reader) =
    reader_projection_clause (f x) (f y) (h s) (g reader)"
  by (simp add: reader_projection_clause_def rename_schema_def map_socket_graph_def)

lemma rename_fixed_result_clause [simp]:
  "rename_schema f h g (fixed_result_clause x s reader v) =
    fixed_result_clause (f x) (h s) (g reader) v"
  by (simp add: fixed_result_clause_def rename_schema_def map_socket_graph_def rename_pattern_def)

lemma reader_projection_instance:
  assumes variables: "x\<noteq>y" and terms: "term_formed p" "term_formed q"
  shows "schema_instance (reader_projection_clause x y s reader)
    {(x,p),(y,q)} p {(s,reader,Pair_Term p q)}"
  using assms by (auto simp: schema_instance_def reader_projection_clause_def schema_formed_def
    schema_variables_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)

theorem reader_projection_rule:
  assumes variables: "x\<noteq>y"
  shows "schema_rule_instance (reader_projection_clause x y s reader) X p \<longleftrightarrow>
    term_formed p \<and> (\<exists>q. term_formed q \<and> (reader,Pair_Term p q)\<in>X)"
proof
  let ?S="reader_projection_clause x y s reader"
  assume rule: "schema_rule_instance ?S X p"
  obtain V Q where inst: "schema_instance ?S V p Q"
    and support: "\<forall>s d t. (s,d,t)\<in>Q \<longrightarrow> (d,t)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  obtain h where assignment: "\<forall>a\<in>schema_variables ?S. (a,h a)\<in>V \<and> term_formed (h a)"
    and head: "p=evaluate_pattern h (schema_conclusion ?S)" and body: "Q=evaluate_schema_premises h ?S"
    using schema_instance_evaluation[OF inst] by blast
  have formed: "term_formed p" using schema_instance_formed[OF inst] by blast
  show "term_formed p \<and> (\<exists>q. term_formed q \<and> (reader,Pair_Term p q)\<in>X)"
    by (rule conjI[OF formed], rule exI[of _ "h y"])
      (use assignment head body support in
        \<open>auto simp: reader_projection_clause_def schema_variables_def evaluate_schema_premises_def\<close>)
next
  let ?S="reader_projection_clause x y s reader"
  assume "term_formed p \<and> (\<exists>q. term_formed q \<and> (reader,Pair_Term p q)\<in>X)"
  then obtain q where parts: "term_formed p" "term_formed q" "(reader,Pair_Term p q)\<in>X" by blast
  have inst: "schema_instance ?S {(x,p),(y,q)} p {(s,reader,Pair_Term p q)}"
    by (rule reader_projection_instance[OF variables parts(1,2)])
  have material: "schema_material_satisfied ?S {(x,p),(y,q)}"
    by (simp add: schema_material_satisfied_def)
  show "schema_rule_instance ?S X p"
    unfolding schema_rule_instance_def
    by (rule exI[of _ "{(x,p),(y,q)}"], rule exI[of _ "{(s,reader,Pair_Term p q)}"])
      (use inst material parts(3) in auto)
qed

theorem fixed_result_rule:
  "schema_rule_instance (fixed_result_clause x s reader v) X p \<longleftrightarrow>
    term_formed v \<and> term_formed p \<and> (reader,Pair_Term p v)\<in>X"
proof
  let ?S="fixed_result_clause x s reader v"
  assume rule: "schema_rule_instance ?S X p"
  obtain V Q where inst: "schema_instance ?S V p Q"
    and support: "\<forall>s d t. (s,d,t)\<in>Q \<longrightarrow> (d,t)\<in>X"
    using rule by (auto simp: schema_rule_instance_def)
  have formed: "term_formed v" and bound: "(x,p)\<in>V"
    and bindings: "term_bindings_formed {x} V"
    using inst by (auto simp: schema_instance_def fixed_result_clause_def schema_variables_def schema_formed_def)
  have premise: "(s,reader,Pair_Term p v)\<in>Q"
    using schema_instance_premise_iff[OF inst, of s reader "Pair_Term p v"] bound formed
    by (simp add: fixed_result_clause_def)
  show "term_formed v \<and> term_formed p \<and> (reader,Pair_Term p v)\<in>X"
    using formed bindings bound support premise by (auto simp: term_bindings_formed_def)
next
  let ?S="fixed_result_clause x s reader v"
  assume parts: "term_formed v \<and> term_formed p \<and> (reader,Pair_Term p v)\<in>X"
  have inst: "schema_instance ?S {(x,p)} p {(s,reader,Pair_Term p v)}"
    using parts by (auto simp: schema_instance_def fixed_result_clause_def schema_variables_def
      schema_formed_def term_bindings_formed_def schema_premise_instance_def single_valued_def rel_dom_def)
  have material: "schema_material_satisfied ?S {(x,p)}"
    by (simp add: schema_material_satisfied_def)
  show "schema_rule_instance ?S X p"
    unfolding schema_rule_instance_def
    by (rule exI[of _ "{(x,p)}"], rule exI[of _ "{(s,reader,Pair_Term p v)}"])
      (use inst material parts in auto)
qed

section \<open>A complete projection family has the same local meaning\<close>

locale reader_projection_profile =
  fixes P :: "('a,'s,'d,'c) schema_system" and entry reader :: 'd
    and x y :: 'a and socket :: 's and clause :: 'c
  assumes system_formed: "schema_system_formed P"
    and variables: "x\<noteq>y"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=clause \<and> S=reader_projection_clause x y socket reader"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,p)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h. term_formed (h x) \<and> term_formed (h y) \<and> p=h x \<and>
      (reader,Pair_Term (h x) (h y))\<in>positive_meaning P)"
proof -
  have accepts: "schema_call_formed P entry
      (evaluate_pattern h (schema_conclusion (reader_projection_clause x y socket reader)))"
    if "\<forall>a\<in>schema_variables (reader_projection_clause x y socket reader). term_formed (h a)" for h
    using that by (auto simp: call reader_projection_clause_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF family reader_projection_clause_ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: reader_projection_clause_def schema_variables_def conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem exact:
  "(entry,p)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>q. (reader,Pair_Term p q)\<in>positive_meaning P)"
proof
  assume "(entry,p)\<in>positive_meaning P"
  then show "\<exists>q. (reader,Pair_Term p q)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>q. (reader,Pair_Term p q)\<in>positive_meaning P"
  then obtain q where read: "(reader,Pair_Term p q)\<in>positive_meaning P" by blast
  have formed: "term_formed p" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
  show "(entry,p)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>a. if a=x then p else q"])
      (use variables read formed in auto)
qed

end

section \<open>Fresh views use the existing program's actual reader\<close>

theorem reader_projection_view:
  assumes source: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and reader: "reader\<in>system_definitions P"
  shows "positive_view P entry (Pattern_Variable i) {(c,reader_projection_clause x y s reader)}"
  by (rule positive_view.intro[OF source fresh])
    (use reader in \<open>auto simp: single_valued_def\<close>)

theorem fixed_result_view:
  assumes source: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and reader: "reader\<in>system_definitions P" and result: "term_formed v"
  shows "positive_view P entry (Pattern_Variable i) {(c,fixed_result_clause x s reader v)}"
  by (rule positive_view.intro[OF source fresh])
    (use reader result in \<open>auto simp: single_valued_def\<close>)

theorem reader_projection_view_meaning:
  assumes view: "positive_view P entry (Pattern_Variable i) {(c,reader_projection_clause x y s reader)}"
    and variables: "x\<noteq>y"
  shows "(entry,p)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,reader_projection_clause x y s reader)}) \<longleftrightarrow>
    (\<exists>q. (reader,Pair_Term p q)\<in>positive_meaning P)"
proof -
  interpret view: positive_view P entry "Pattern_Variable i" "{(c,reader_projection_clause x y s reader)}"
    by (rule view)
  interpret projection: reader_projection_profile
    "add_view_definition P entry (Pattern_Variable i) {(c,reader_projection_clause x y s reader)}"
    entry reader x y s c
    by (unfold_locales)
      (use view.formed variables view.no_old_clause view.view_call in auto)
  have member: "reader\<in>system_definitions P" using view.callees by simp
  show ?thesis by (simp only: projection.exact view.old_meaning[OF member])
qed

theorem fixed_result_view_meaning:
  assumes view: "positive_view P entry (Pattern_Variable i) {(c,fixed_result_clause x s reader v)}"
  shows "(entry,p)\<in>positive_meaning
      (add_view_definition P entry (Pattern_Variable i) {(c,fixed_result_clause x s reader v)}) \<longleftrightarrow>
    (reader,Pair_Term p v)\<in>positive_meaning P"
proof -
  interpret view: positive_view P entry "Pattern_Variable i" "{(c,fixed_result_clause x s reader v)}"
    by (rule view)
  have formed: "term_formed p \<and> term_formed v"
    if "(reader,Pair_Term p v)\<in>positive_meaning P"
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by simp
  show ?thesis using view.view_meaning[of p] formed by (auto simp: fixed_result_rule)
qed

theorem reader_projection_view_exists:
  fixes P :: "('a,'s,nat,'c) schema_system"
  assumes source: "schema_system_formed P" and reader: "reader\<in>system_definitions P"
  shows "\<exists>entry. positive_view P entry (Pattern_Variable i) {(c,reader_projection_clause x y s reader)}"
  by (rule positive_view_exists[OF source])
    (use reader in \<open>auto simp: single_valued_def\<close>)

theorem fixed_result_view_exists:
  fixes P :: "('a,'s,nat,'c) schema_system"
  assumes source: "schema_system_formed P" and reader: "reader\<in>system_definitions P"
    and result: "term_formed v"
  shows "\<exists>entry. positive_view P entry (Pattern_Variable i) {(c,fixed_result_clause x s reader v)}"
  by (rule positive_view_exists[OF source])
    (use reader result in \<open>auto simp: single_valued_def\<close>)

text \<open>
  Projection and fixed-result checking are ordinary one-premise rules. The
  reader is an actual callee, the premise occurrence has its own socket, and
  the result is either a private variable or literal pattern data. Distinct
  source and result variables are required for the projection equation.

  Their rule equations hold for every supporting relation and every term.
  Fresh views preserve the old program and inherit its actual reader meaning.
  The fixed-result schema generalizes the earlier reference-checking clause;
  its literal argument need not be a schema report.
\<close>

end
