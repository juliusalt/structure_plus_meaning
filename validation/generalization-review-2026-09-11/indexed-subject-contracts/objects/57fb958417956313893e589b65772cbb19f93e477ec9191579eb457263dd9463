theory Factor_Context_Pairing
  imports Factor_Related_List_Maps
begin

section \<open>Pair construction retains independently admitted operands\<close>

definition paired_terms_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "paired_terms_schema first second=data_rule
    (context_relation_pattern data_x data_y (Pattern_Pair data_x data_y))
    {(0,first,data_x),(1,second,data_y)}"

lemma paired_terms_formed [simp]: "schema_formed (paired_terms_schema first second)"
  by (auto simp: paired_terms_schema_def schema_formed_def single_valued_def)

lemma paired_terms_dependencies [simp]:
  "schema_dependencies (paired_terms_schema first second)={first,second}"
  by (auto simp: paired_terms_schema_def schema_dependencies_def rel_ran_image)

locale paired_terms_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry first second :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=paired_terms_schema first second"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and>
      t=context_relation_argument (h 0) (h 1) (Pair_Term (h 0) (h 1)) \<and>
      (first,h 0)\<in>positive_meaning P \<and> (second,h 1)\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family paired_terms_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>x y. t=context_relation_argument x y (Pair_Term x y) \<and>
      (first,x)\<in>positive_meaning P \<and> (second,y)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>x y. t=context_relation_argument x y (Pair_Term x y) \<and>
      (first,x)\<in>positive_meaning P \<and> (second,y)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>x y. t=context_relation_argument x y (Pair_Term x y) \<and>
      (first,x)\<in>positive_meaning P \<and> (second,y)\<in>positive_meaning P"
  then obtain x y where parts: "t=context_relation_argument x y (Pair_Term x y)"
    "(first,x)\<in>positive_meaning P" "(second,y)\<in>positive_meaning P" by blast
  have terms: "term_formed x" "term_formed y"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]]
      schema_call_formed_target[OF positive_meaning_formed[OF parts(3)]] by blast+
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then x else y"])
      (use parts terms in auto)
qed

corollary at_input:
  "(entry,context_relation_argument x y q)\<in>positive_meaning P \<longleftrightarrow>
    (first,x)\<in>positive_meaning P \<and> (second,y)\<in>positive_meaning P \<and> q=Pair_Term x y"
  by (auto simp only: exact factor_term.inject)

end

section \<open>A transposed call keeps the result and exchanges its two input roles\<close>

definition transposed_context_schema :: "nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "transposed_context_schema operation=data_rule (context_relation_pattern data_x data_y data_z)
    {(0,operation,context_relation_pattern data_y data_x data_z)}"

lemma transposed_context_formed [simp]: "schema_formed (transposed_context_schema operation)"
  by (auto simp: transposed_context_schema_def schema_formed_def single_valued_def)

lemma transposed_context_dependencies [simp]:
  "schema_dependencies (transposed_context_schema operation)={operation}"
  by (auto simp: transposed_context_schema_def schema_dependencies_def rel_ran_image)

locale transposed_context_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry operation :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=transposed_context_schema operation"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=context_relation_argument (h 0) (h 1) (h 2) \<and>
      (operation,context_relation_argument (h 1) (h 0) (h 2))\<in>positive_meaning P)"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: family transposed_context_schema_def schema_variables_def call)

theorem exact:
  "(entry,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>x y q. t=context_relation_argument x y q \<and>
      (operation,context_relation_argument y x q)\<in>positive_meaning P)"
proof
  assume "(entry,t)\<in>positive_meaning P"
  then show "\<exists>x y q. t=context_relation_argument x y q \<and>
      (operation,context_relation_argument y x q)\<in>positive_meaning P"
    by (simp only: valuation) blast
next
  assume "\<exists>x y q. t=context_relation_argument x y q \<and>
      (operation,context_relation_argument y x q)\<in>positive_meaning P"
  then obtain x y q where parts: "t=context_relation_argument x y q"
    "(operation,context_relation_argument y x q)\<in>positive_meaning P" by blast
  have terms: "term_formed x" "term_formed y" "term_formed q"
    using schema_call_formed_target[OF positive_meaning_formed[OF parts(2)]] by auto
  show "(entry,t)\<in>positive_meaning P"
    by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then x else if i=1 then y else q"])
      (use parts terms in auto)
qed

corollary at_input:
  "(entry,context_relation_argument x y q)\<in>positive_meaning P \<longleftrightarrow>
    (operation,context_relation_argument y x q)\<in>positive_meaning P"
  by (auto simp only: exact factor_term.inject)

end

text \<open>
  Each construction is an ordinary native clause with its actual callee
  coordinates and premise sockets. Pair construction retains both literal
  terms and their independently supplied admission conditions. Transposition
  changes which operand plays the shared context role; it changes neither
  the callee's domain nor the order of fields in its result.
\<close>

end
