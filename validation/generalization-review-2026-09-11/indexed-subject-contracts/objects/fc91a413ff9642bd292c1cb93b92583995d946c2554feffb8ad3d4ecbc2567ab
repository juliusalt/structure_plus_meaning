theory Factor_Observation_Scope_Investigation
  imports Factor_Observation_Scope_Admission Finite_Investigation_Interface
begin

section \<open>Whole input admission is compared with two actual native decisions\<close>

abbreviation observation_scope_example_zero where
  "observation_scope_example_zero \<equiv> Payload_Term [0]"

abbreviation observation_scope_example_reference where
  "observation_scope_example_reference \<equiv> Target_Term (Whole_Artifact empty_artifact)"

definition observation_scope_example_candidates :: "nat \<Rightarrow> factor_term list" where
  "observation_scope_example_candidates n=
    [if n=1 then observation_scope_example_reference else observation_scope_example_zero]"

definition observation_scope_example_facets :: "nat \<Rightarrow> factor_term list" where
  "observation_scope_example_facets n=
    [if n=2 then observation_scope_example_reference else observation_scope_example_zero]"

definition observation_scope_example_selected :: "nat \<Rightarrow> factor_term list" where
  "observation_scope_example_selected n=(if n=3 then [Payload_Term [1]] else [])"

definition observation_scope_example_table :: "nat \<Rightarrow> (factor_term\<times>factor_term\<times>factor_term) list" where
  "observation_scope_example_table n=(if n=4 then
      [(Payload_Term [1],observation_scope_example_zero,observation_scope_example_zero)]
    else if n=5 then [(observation_scope_example_zero,Payload_Term [1],observation_scope_example_zero)]
    else if n=6 then [(observation_scope_example_zero,observation_scope_example_zero,observation_scope_example_zero)]
    else [])"

abbreviation observation_scope_example_argument where
  "observation_scope_example_argument n \<equiv>
    observation_scope_argument (data_list_term (observation_scope_example_candidates n))
      (data_list_term (observation_scope_example_facets n)) (data_list_term (observation_scope_example_selected n))
      (data_list_term (map observation_row_term (observation_scope_example_table n)))"

lemmas observation_scope_example_defs=observation_scope_example_candidates_def observation_scope_example_facets_def
  observation_scope_example_selected_def observation_scope_example_table_def

lemma observation_scope_example_formed:
  "schema_call_formed observation_scope_system 309 (observation_scope_example_argument n)"
  by (auto simp: observation_scope_call observation_scope_example_defs data_list_term_formed
    octets_formed_def split: if_splits)

definition observation_scope_example_admitted :: "nat \<Rightarrow> bool" where
  "observation_scope_example_admitted n \<longleftrightarrow>
    observation_scope_subject_formed (fset_of_list (observation_scope_example_candidates n))
      (fset_of_list (observation_scope_example_facets n)) (fset_of_list (observation_scope_example_selected n))
      (fset_of_list (observation_scope_example_table n))"

lemma observation_scope_example_admitted_code [code]:
  "observation_scope_example_admitted n \<longleftrightarrow> n=0 \<or> 6\<le>n"
  unfolding observation_scope_example_admitted_def
  by (subst observation_scope_subject_lists)
    (auto simp: observation_scope_example_defs octets_formed_def split: if_splits)

definition scope_investigation_decision :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "scope_investigation_decision f n=(if f=0 then
    (309,observation_scope_example_argument n)\<in>positive_meaning observation_scope_system
    else (311,observation_scope_example_argument n)\<in>positive_meaning observation_scope_system)"

lemma observation_scope_example_rows_decision:
  "(309,observation_scope_example_argument n)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
    n\<noteq>4 \<and> n\<noteq>5"
  by (subst observation_scope_rows_encoded)
    (auto simp: observation_scope_example_defs data_list_term_formed octets_formed_def split: if_splits)

lemma scope_investigation_decision_code [code]:
  "scope_investigation_decision f n=(if f=0 then n\<noteq>4 \<and> n\<noteq>5 else n=0 \<or> 6\<le>n)"
  by (simp only: scope_investigation_decision_def observation_scope_example_rows_decision observation_scope_encoded
    observation_scope_example_admitted_def[symmetric] observation_scope_example_admitted_code)

lemma observation_scope_example_complete_formed:
  "schema_call_formed observation_scope_system 311 (observation_scope_example_argument n)"
  by (auto simp: observation_scope_call observation_scope_example_defs data_list_term_formed
    octets_formed_def split: if_splits)

definition scope_investigation_compare :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "scope_investigation_compare c d \<longleftrightarrow>
    observation_scope_example_admitted c=observation_scope_example_admitted d"

definition scope_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "scope_investigation_observations=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,if scope_investigation_decision f c then 1 else 0)) [0,1]) [0,1,2,3,4,5,6])"

definition scope_investigation_relation :: "(nat\<times>nat) list" where
  "scope_investigation_relation=filter (\<lambda>(c,d). scope_investigation_compare c d)
    (investigation_pairs [0,1,2,3,4,5,6])"

lemma scope_investigation_relation_exact:
  "(c,d)\<in>set scope_investigation_relation \<longleftrightarrow>
    c\<in>{0,1,2,3,4,5,6} \<and> d\<in>{0,1,2,3,4,5,6} \<and>
    observation_scope_example_admitted c=observation_scope_example_admitted d"
  by (simp only: scope_investigation_relation_def set_filter investigation_pairs_exact
    mem_Collect_eq case_prod_conv scope_investigation_compare_def list.set; blast)

definition scope_investigation where
  "scope_investigation selected=investigation_basis [0,1,2,3,4,5,6] [0,1] selected
    scope_investigation_observations scope_investigation_relation"

export_code investigation_inference investigation_basis investigation_repairs investigation_extend scope_investigation
  scope_investigation_observations scope_investigation_relation nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

end
