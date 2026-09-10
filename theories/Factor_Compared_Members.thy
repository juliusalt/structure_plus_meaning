theory Factor_Compared_Members
  imports Factor_List_Profiles
begin

section \<open>An actual membership call supplies a comparison witness\<close>

definition compared_member_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "compared_member_schema member compare=data_rule (Pattern_Pair data_x data_y)
    {(0,member,Pattern_Pair data_x data_z),(1,compare,Pattern_Pair data_y data_z)}"

definition reverse_compared_member_schema :: "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "reverse_compared_member_schema member compare=data_rule (Pattern_Pair data_x data_y)
    {(0,member,Pattern_Pair data_x data_z),(1,compare,Pattern_Pair data_z data_y)}"

lemma compared_member_schemas_formed [simp]:
  "schema_formed (compared_member_schema member compare)"
  "schema_formed (reverse_compared_member_schema member compare)"
  by (auto simp: compared_member_schema_def reverse_compared_member_schema_def
    schema_formed_def single_valued_def)

lemma compared_member_schemas_dependencies [simp]:
  "schema_dependencies (compared_member_schema member compare)={member,compare}"
  "schema_dependencies (reverse_compared_member_schema member compare)={member,compare}"
  by (auto simp: compared_member_schema_def reverse_compared_member_schema_def
    schema_dependencies_def rel_ran_image)

locale compared_member_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and member compare forward backward :: nat
  assumes formed: "schema_system_formed P"
    and forward_family: "\<And>c S. ((forward,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=compared_member_schema member compare"
    and backward_family: "\<And>c S. ((backward,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=reverse_compared_member_schema member compare"
    and forward_call: "\<And>t. schema_call_formed P forward t \<longleftrightarrow> term_formed t"
    and backward_call: "\<And>t. schema_call_formed P backward t \<longleftrightarrow> term_formed t"
    and membership: "\<And>t. (member,t)\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and> x\<in>set xs)"
begin

abbreviation related where
  "related x y \<equiv> (compare,Pair_Term x y)\<in>positive_meaning P"

lemma forward_valuation:
  "(forward,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (member,Pair_Term (h 0) (h 2))\<in>positive_meaning P \<and>
      related (h 1) (h 2))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: forward_family compared_member_schema_def schema_variables_def forward_call)

lemma backward_valuation:
  "(backward,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. term_formed (h 0) \<and> term_formed (h 1) \<and> term_formed (h 2) \<and>
      t=Pair_Term (h 0) (h 1) \<and> (member,Pair_Term (h 0) (h 2))\<in>positive_meaning P \<and>
      related (h 2) (h 1))"
  by (subst ordinary_positive_entry_valuation)
    (auto simp: backward_family reverse_compared_member_schema_def schema_variables_def backward_call)

lemma comparison_formed:
  assumes "related x y"
  shows "term_formed x \<and> term_formed y"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by auto

theorem forward_exact:
  "(forward,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and>
      (\<exists>y\<in>set xs. related x y))"
proof
  assume "(forward,t)\<in>positive_meaning P"
  then show "\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and>
      (\<exists>y\<in>set xs. related x y)"
    by (simp only: forward_valuation membership; blast)
next
  assume "\<exists>xs x. t=Pair_Term (data_list_term xs) x \<and> data_elements xs \<and>
      (\<exists>y\<in>set xs. related x y)"
  then obtain xs x y where parts: "t=Pair_Term (data_list_term xs) x" "data_elements xs"
    "y\<in>set xs" "related x y" by blast
  show "(forward,t)\<in>positive_meaning P"
    by (simp only: forward_valuation;
      rule exI[of _ "\<lambda>i::nat. if i=0 then data_list_term xs else if i=1 then x else y"])
      (use parts comparison_formed[OF parts(4)] in \<open>auto simp: membership data_list_term_formed\<close>)
qed

theorem backward_exact:
  "(backward,t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>xs y. t=Pair_Term (data_list_term xs) y \<and> data_elements xs \<and>
      (\<exists>x\<in>set xs. related x y))"
proof
  assume "(backward,t)\<in>positive_meaning P"
  then show "\<exists>xs y. t=Pair_Term (data_list_term xs) y \<and> data_elements xs \<and>
      (\<exists>x\<in>set xs. related x y)"
    by (simp only: backward_valuation membership; blast)
next
  assume "\<exists>xs y. t=Pair_Term (data_list_term xs) y \<and> data_elements xs \<and>
      (\<exists>x\<in>set xs. related x y)"
  then obtain xs y x where parts: "t=Pair_Term (data_list_term xs) y" "data_elements xs"
    "x\<in>set xs" "related x y" by blast
  show "(backward,t)\<in>positive_meaning P"
    by (simp only: backward_valuation;
      rule exI[of _ "\<lambda>i::nat. if i=0 then data_list_term xs else if i=1 then y else x"])
      (use parts comparison_formed[OF parts(4)] in \<open>auto simp: membership data_list_term_formed\<close>)
qed

corollary forward_at:
  "(forward,Pair_Term (data_list_term xs) x)\<in>positive_meaning P \<longleftrightarrow>
    data_elements xs \<and> (\<exists>y\<in>set xs. related x y)"
  by (auto simp only: forward_exact factor_term.inject data_list_term_injective)

corollary backward_at:
  "(backward,Pair_Term (data_list_term xs) y)\<in>positive_meaning P \<longleftrightarrow>
    data_elements xs \<and> (\<exists>x\<in>set xs. related x y)"
  by (auto simp only: backward_exact factor_term.inject data_list_term_injective)

end

text \<open>
  The selected member is an ordinary premise-only variable. Membership checks
  its whole supplied list; comparison checks that member and the supplied
  element. The second schema reverses which element is selected, while both
  meanings preserve the comparison's left and right operands. The callee
  need not be symmetric, and may share a positive dependency cycle with
  these definitions. Its actual meaning remains the comparison relation.
\<close>

end
