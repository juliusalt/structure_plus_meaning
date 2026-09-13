theory Factor_Admission_Pair_Schemas
  imports Factor_Data_Comparison Factor_Clause_Family_Rules
begin

definition admitted_pair_schema :: "'d \<Rightarrow> 'd \<Rightarrow> (nat,nat,'d) factor_schema" where
  "admitted_pair_schema first second=data_rule (Pattern_Pair data_x data_y)
    {(0,first,data_x),(1,second,data_y)}"

lemma admitted_pair_formed [simp]: "schema_formed (admitted_pair_schema first second)"
  by (auto simp: admitted_pair_schema_def schema_formed_def single_valued_def)

lemma admitted_pair_dependencies [simp]: "schema_dependencies (admitted_pair_schema first second)={first,second}"
  by (auto simp: admitted_pair_schema_def schema_dependencies_def rel_ran_image)

lemma admitted_data_pair_schema: "admitted_pair_schema 2 2=data_pair_schema"
  by (simp only: admitted_pair_schema_def data_pair_schema_def)

lemma admitted_pair_rule_instance:
  "schema_rule_instance (admitted_pair_schema a b) M t \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> term_formed x \<and> term_formed y \<and> (a,x)\<in>M \<and> (b,y)\<in>M)"
proof -
  have ordinary: "schema_material_premises (admitted_pair_schema a b)={}"
    by (simp add: admitted_pair_schema_def)
  have valuation: "schema_rule_instance (admitted_pair_schema a b) M t \<longleftrightarrow>
    (\<exists>f::nat\<Rightarrow>factor_term. term_formed (f 0) \<and> term_formed (f 1) \<and>
      t=Pair_Term (f 0) (f 1) \<and> (a,f 0)\<in>M \<and> (b,f 1)\<in>M)"
    by (simp only: ordinary_schema_rule_valuation[OF admitted_pair_formed ordinary];
      auto simp: admitted_pair_schema_def schema_variables_def)
  show ?thesis
  proof
    assume "schema_rule_instance (admitted_pair_schema a b) M t"
    then show "\<exists>x y. t=Pair_Term x y \<and> term_formed x \<and> term_formed y \<and> (a,x)\<in>M \<and> (b,y)\<in>M"
      by (simp only: valuation; blast)
  next
    assume "\<exists>x y. t=Pair_Term x y \<and> term_formed x \<and> term_formed y \<and> (a,x)\<in>M \<and> (b,y)\<in>M"
    then obtain x y where fields: "t=Pair_Term x y" "term_formed x" "term_formed y" "(a,x)\<in>M" "(b,y)\<in>M" by blast
    show "schema_rule_instance (admitted_pair_schema a b) M t"
      by (simp only: valuation; rule exI[of _ "\<lambda>i::nat. if i=0 then x else y"])
        (use fields in simp)
  qed
qed

lemma admitted_pair_positive_rule:
  "schema_rule_instance (admitted_pair_schema a b) (positive_meaning P) t \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning P \<and> (b,y)\<in>positive_meaning P)"
proof -
  have formed: "term_formed x" if "(d,x)\<in>positive_meaning P" for d x
    using schema_call_formed_target[OF positive_meaning_formed[OF that]] by blast
  show ?thesis by (simp only: admitted_pair_rule_instance; use formed in blast)
qed

theorem admitted_pair_rule_family:
  assumes call: "\<And>t. schema_call_formed P d t \<longleftrightarrow> term_formed t"
    and family: "\<And>t. (\<exists>c S. (c,S)\<in>system_clause_family P d \<and> schema_rule_instance S (positive_meaning P) t)
      \<longleftrightarrow> schema_rule_instance (admitted_pair_schema a b) (positive_meaning P) t"
  shows "(d,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> (a,x)\<in>positive_meaning P \<and> (b,y)\<in>positive_meaning P)"
  by (simp only: positive_variable_rule_family[OF call] family admitted_pair_positive_rule)

end
