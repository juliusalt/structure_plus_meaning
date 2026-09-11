theory Factor_Investigation_Input_Investigation
  imports Factor_Investigation_Input_Execution Finite_Investigation_Interface
begin

section \<open>Restricting both comparison endpoints is an additional requirement\<close>

lemma investigation_basis_formation_ignores_comparison:
  "fst (investigation_basis C U F T R)=fst (investigation_basis C U F T R')"
  by (simp only: investigation_basis_formation)

abbreviation input_example_candidates where
  "input_example_candidates n \<equiv> if n=9 \<or> n=10 then [] else [observation_octet 0,observation_octet 1]"

abbreviation input_example_facets where
  "input_example_facets n \<equiv> [if n=10 then observation_reference else observation_octet 0]"

abbreviation input_example_selected where
  "input_example_selected n \<equiv> if n=9 \<or> n=10 then [] else [observation_octet (if n=8 then 1 else 0)]"

abbreviation input_example_rows where
  "input_example_rows n \<equiv> if n=9 \<or> n=10 then [] else [(observation_octet 0,observation_octet 0,observation_octet 0)]"

definition input_example_relation :: "nat \<Rightarrow> (factor_term\<times>factor_term) list" where
  "input_example_relation n=(if n=1 then [(observation_octet 1,observation_octet 1),
      (observation_octet 0,observation_octet 0),(observation_octet 1,observation_octet 1)]
    else if n=2 then [(observation_octet 2,observation_octet 0)]
    else if n=3 then [(observation_octet 0,observation_octet 2)]
    else if n=4 \<or> n=9 then [(observation_octet 2,observation_octet 2)]
    else if n=5 \<or> n=8 \<or> n=10 then []
    else if n=6 then [(observation_reference,observation_octet 0)]
    else if n=7 then [(observation_octet 0,observation_reference)]
    else [(observation_octet 0,observation_octet 0),(observation_octet 1,observation_octet 1)])"

abbreviation input_example_scope where
  "input_example_scope n \<equiv> observation_scope_argument (data_list_term (input_example_candidates n))
    (data_list_term (input_example_facets n)) (data_list_term (input_example_selected n))
    (data_list_term (map observation_row_term (input_example_rows n)))"

abbreviation input_example_endpoint_scope where
  "input_example_endpoint_scope n swapped \<equiv>
    observation_scope_argument (data_list_term (input_example_candidates n)) (data_list_term [Payload_Term []])
      (data_list_term []) (data_list_term (map observation_row_term
        (map (\<lambda>(c,d). if swapped then (Payload_Term [],d,c) else (Payload_Term [],c,d)) (input_example_relation n))))"

definition input_investigation_decision :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "input_investigation_decision f n \<longleftrightarrow> (if f=0 then
    (311,input_example_scope n)\<in>positive_meaning observation_scope_system \<and>
    (311,input_example_endpoint_scope n False)\<in>positive_meaning observation_scope_system \<and>
    (311,input_example_endpoint_scope n True)\<in>positive_meaning observation_scope_system
    else (338,Pair_Term (input_example_scope n) (data_list_term (map data_pair_term (input_example_relation n))))
      \<in>positive_meaning investigation_input_system)"

definition input_example_admitted :: "nat \<Rightarrow> bool" where
  "input_example_admitted n \<longleftrightarrow>
    investigation_input_subject_formed (fset_of_list (input_example_candidates n))
      (fset_of_list (input_example_facets n)) (fset_of_list (input_example_selected n))
      (fset_of_list (input_example_rows n)) (fset_of_list (input_example_relation n))"

lemma input_example_admitted_code [code]:
  "input_example_admitted n \<longleftrightarrow> n\<notin>{6,7,8,10}"
  unfolding input_example_admitted_def
  by (simp only: investigation_input_subject_lists observation_scope_subject_lists)
    (auto simp: input_example_relation_def octets_formed_def split: if_splits)

lemma input_investigation_decision_code [code]:
  "input_investigation_decision f n \<longleftrightarrow>
    (if f=0 then n\<notin>{2,3,4,6,7,8,9,10} else input_example_admitted n)"
proof -
  have restricted: "(311,input_example_scope n)\<in>positive_meaning observation_scope_system \<and>
      (311,input_example_endpoint_scope n False)\<in>positive_meaning observation_scope_system \<and>
      (311,input_example_endpoint_scope n True)\<in>positive_meaning observation_scope_system \<longleftrightarrow>
      n\<notin>{2,3,4,6,7,8,9,10}"
    by (simp only: observation_scope_encoded observation_scope_subject_lists)
      (auto simp: input_example_relation_def octets_formed_def split: if_splits)
  show ?thesis by (simp only: input_investigation_decision_def restricted investigation_input_encoded input_example_admitted_def)
qed

lemma input_example_calls_formed:
  "schema_call_formed observation_scope_system 311 (input_example_scope n)"
  "schema_call_formed observation_scope_system 311 (input_example_endpoint_scope n swapped)"
  "schema_call_formed investigation_input_system 338
    (Pair_Term (input_example_scope n) (data_list_term (map data_pair_term (input_example_relation n))))"
  by (auto simp: observation_scope_call investigation_input_call input_example_relation_def
    data_list_term_formed octets_formed_def split: if_splits)

definition input_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "input_investigation_observations=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,if input_investigation_decision f c then 1 else 0)) [0,1]) [0,1,2,3,4,5,6,7,8,9,10])"

definition input_investigation_relation :: "(nat\<times>nat) list" where
  "input_investigation_relation=filter (\<lambda>(c,d). input_example_admitted c=input_example_admitted d)
    (investigation_pairs [0,1,2,3,4,5,6,7,8,9,10])"

lemma input_investigation_relation_exact:
  "(c,d)\<in>set input_investigation_relation \<longleftrightarrow>
    c\<in>{0,1,2,3,4,5,6,7,8,9,10} \<and> d\<in>{0,1,2,3,4,5,6,7,8,9,10} \<and>
      input_example_admitted c=input_example_admitted d"
  by (simp only: input_investigation_relation_def set_filter investigation_pairs_exact
    mem_Collect_eq case_prod_conv list.set; blast)

definition input_investigation where
  "input_investigation selected=investigation_basis [0,1,2,3,4,5,6,7,8,9,10] [0,1] selected
    input_investigation_observations input_investigation_relation"

export_code investigation_inference investigation_basis investigation_repairs investigation_extend input_investigation
  input_investigation_observations input_investigation_relation nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

text \<open>
  The observation calls the actual native declared-scope operation on the
  original scope and on both endpoint orientations of the comparison rows.
  This proposed additional check requires both endpoints to be declared
  candidates. The independent input class retains the whole data relation
  without that restriction. Its eleven subjects include changed presentations,
  foreign endpoints, malformed references, an unavailable selected facet,
  an empty candidate set with a nonempty comparison, and malformed unused
  scope data. A second observation calls the complete native input operation
  on those same subjects. All calls are formed, including the reference
  controls. The investigation compares complete admission outcomes.
\<close>

end
